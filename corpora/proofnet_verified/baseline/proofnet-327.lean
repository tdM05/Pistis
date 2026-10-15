import Mathlib

set_option maxHeartbeats 800000

open scoped BigOperators
open Filter Topology Set

/-Informal Statement

Let $f$ be a real function with a continuous third derivative such that $f(x), f^{\prime}(x), f^{\prime \prime}(x), f^{\prime \prime \prime}(x)$ are positive for all $x$. Suppose that $f^{\prime \prime \prime}(x) \leq f(x)$ for all $x$. Show that $f^{\prime}(x)<2 f(x)$ for all $x$.
-/

/-Informal Proof

\setcounter{equation}{0}
We make repeated use of the following fact: if $f$ is a differentiable function on all of
$\mathbb{R}$, $\lim_{x \to -\infty} f(x) \geq 0$, and $f'(x) > 0$ for all $x \in \mathbb{R}$, then
$f(x) > 0$ for all $x \in \mathbb{R}$. (Proof: if $f(y) < 0$ for some $x$, then $f(x)< f(y)$ for all
$x<y$ since $f'>0$, but then $\lim_{x \to -\infty} f(x) \leq f(y) < 0$.)

From the inequality $f'''(x) \leq f(x)$ we obtain
\[
f'' f'''(x) \leq f''(x) f(x) < f''(x) f(x) + f'(x)^2
\]
since $f'(x)$ is positive. Applying the fact to the difference between the right and left sides,
we get
\begin{equation}
\frac{1}{2} (f''(x))^2 < f(x) f'(x).
\end{equation}

On the other hand, since $f(x)$ and $f'''(x)$ are both positive for all $x$,
we have
\[
2f'(x) f''(x) < 2f'(x)f''(x) + 2f(x) f'''(x).
\]
Applying the fact to the difference between the sides yields
\begin{equation}
f'(x)^2 \leq 2f(x) f''(x).
\end{equation}
Combining (1) and (2), we obtain
\begin{align*}
\frac{1}{2} \left( \frac{f'(x)^2}{2f(x)} \right)^2
&< \frac{1}{2} (f''(x))^2 \\
&< f(x) f'(x),
\end{align*}
or $(f'(x))^3 < 8 f(x)^3$. We conclude $f'(x) < 2f(x)$, as desired.
-/

/-
================================================================================
AUXILIARY LEMMAS
================================================================================
-/

/--
Key Lemma: If g is strictly increasing and bounded below,
and sInf (range g) ≥ 0, then g(x) > 0 for all x.

This is because for a strictly monotone function, the infimum is never attained,
so g(x) > sInf (range g) ≥ 0.
-/
lemma pos_of_strictMono_bddBelow_inf_nonneg {g : ℝ → ℝ}
    (hg_mono : StrictMono g)
    (hg_bdd : BddBelow (range g))
    (h_inf : sInf (range g) ≥ 0) :
    ∀ x : ℝ, g x > 0 := by
  -- Step 1: Prove by showing g(x) > sInf (range g) ≥ 0
  intro x

  -- Step 2: Get that g(x) ≥ sInf (range g)
  have hgx_ge_inf : g x ≥ sInf (range g) := by
    apply csInf_le hg_bdd
    exact mem_range_self x

  -- Step 3: We need g(x) > sInf (range g), not just ≥
  -- Use strict monotonicity: g(x-1) < g(x), and g(x-1) ≥ sInf
  have h_strict : g (x - 1) < g x := hg_mono (by linarith : x - 1 < x)
  have hgx1_ge_inf : g (x - 1) ≥ sInf (range g) := by
    apply csInf_le hg_bdd
    exact mem_range_self (x - 1)

  -- Step 4: So sInf ≤ g(x-1) < g(x)
  have : sInf (range g) < g x := by linarith

  -- Step 5: Combined with h_inf: sInf ≥ 0, so g(x) > sInf ≥ 0
  linarith

theorem Putnam_exercise_1999_b4 (f : ℝ → ℝ) (hf: ContDiff ℝ 3 f)
  (hf1 : ∀ n ≤ 3, ∀ x : ℝ, iteratedDeriv n f x > 0)
  (hf2 : ∀ x : ℝ, iteratedDeriv 3 f x ≤ f x) :
  ∀ x : ℝ, deriv f x < 2 * f x := by
  /-
  ================================================================================
  PROOF OVERVIEW (Putnam 1999 B4)
  ================================================================================

  We prove that f'(x) < 2f(x) for all x, given:
  - f is C³
  - f(x), f'(x), f''(x), f'''(x) are all positive for all x
  - f'''(x) ≤ f(x) for all x

  The proof uses the following key inequalities derived from limit arguments:
  1. (f'')² < 2ff'   (from g = ff' - (1/2)(f'')² having g' > 0 and lim_{x→-∞} g = 0)
  2. (f')² < 2ff''   (from h = 2ff'' - (f')² having h' > 0 and lim_{x→-∞} h = 0)

  Combining these: (f')⁴/(4f²) < (f'')² < 2ff', so (f')³ < 8f³, hence f' < 2f.
  ================================================================================
  -/

  -- Step 1: Extract positivity conditions for each derivative
  have hf_pos : ∀ x : ℝ, f x > 0 := by
    intro x
    have h := hf1 0 (by norm_num : (0 : ℕ) ≤ 3) x
    simp only [iteratedDeriv_zero] at h
    exact h

  have hf'_pos : ∀ x : ℝ, deriv f x > 0 := by
    intro x
    have h := hf1 1 (by norm_num : (1 : ℕ) ≤ 3) x
    rw [iteratedDeriv_one] at h
    exact h

  have hf''_pos : ∀ x : ℝ, iteratedDeriv 2 f x > 0 := fun x => hf1 2 (by norm_num) x

  have hf'''_pos : ∀ x : ℝ, iteratedDeriv 3 f x > 0 := fun x => hf1 3 (le_refl 3) x

  have hf''_eq : ∀ x, iteratedDeriv 2 f x = deriv (deriv f) x := by
    intro x; rw [iteratedDeriv_succ, iteratedDeriv_one]

  have hf'''_eq : ∀ x, iteratedDeriv 3 f x = deriv (deriv (deriv f)) x := by
    intro x; rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]

  -- Step 2: Establish differentiability
  have hf_diff : Differentiable ℝ f := hf.differentiable (by decide)

  have hf'_diff : Differentiable ℝ (deriv f) := by
    have h : ContDiff ℝ 2 (deriv f) := (contDiff_succ_iff_deriv.mp hf).2.2
    exact h.differentiable (by decide)

  have hf''_diff : Differentiable ℝ (deriv (deriv f)) := by
    have h1 : ContDiff ℝ 2 (deriv f) := (contDiff_succ_iff_deriv.mp hf).2.2
    have h2 : ContDiff ℝ 1 (deriv (deriv f)) := (contDiff_succ_iff_deriv.mp h1).2.2
    exact h2.differentiable (by decide)

  -- Step 3: Establish strict monotonicity
  have hf_strictMono : StrictMono f := strictMono_of_deriv_pos hf'_pos

  have hf'_strictMono : StrictMono (deriv f) := by
    apply strictMono_of_deriv_pos
    intro x; rw [← hf''_eq]; exact hf''_pos x

  have hf''_strictMono : StrictMono (deriv (deriv f)) := by
    apply strictMono_of_deriv_pos
    intro x; rw [← hf'''_eq]; exact hf'''_pos x

  -- Step 4: Key facts about infima
  have hf'_bddBelow : BddBelow (range (deriv f)) := by
    use 0; intro y hy; obtain ⟨x, hx⟩ := hy; rw [← hx]; exact le_of_lt (hf'_pos x)

  have hf''_bddBelow : BddBelow (range (deriv (deriv f))) := by
    use 0; intro y hy; obtain ⟨x, hx⟩ := hy; rw [← hx, ← hf''_eq]; exact le_of_lt (hf''_pos x)

  have hf'_inf_nonneg : sInf (range (deriv f)) ≥ 0 := by
    apply le_csInf (range_nonempty _)
    intro y hy; obtain ⟨x, hx⟩ := hy; rw [← hx]; exact le_of_lt (hf'_pos x)

  -- Step 4.1: sInf(range f') = 0 (proven by contradiction using MVT)
  have hf'_inf_eq_zero : sInf (range (deriv f)) = 0 := by
    apply le_antisymm
    · by_contra h_pos; push_neg at h_pos
      set c := sInf (range (deriv f))
      have hc_pos : c > 0 := h_pos
      have hf'_ge_c : ∀ x, deriv f x ≥ c := fun x => csInf_le hf'_bddBelow (mem_range_self x)
      have hf0_pos : f 0 > 0 := hf_pos 0
      set x₀ := -f 0 / c - 1
      have hx0_neg : x₀ < 0 := by
        have : -f 0 / c < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hf0_pos) hc_pos
        linarith
      -- MVT gives f(0) - f(x₀) ≥ c*(0-x₀)
      have h_mvt : f 0 - f x₀ ≥ c * (0 - x₀) := by
        have h_diff_on : DifferentiableOn ℝ f (Ioo x₀ 0) :=
          hf_diff.differentiableOn.mono Ioo_subset_Icc_self
        have h_cont_on : ContinuousOn f (Icc x₀ 0) := hf_diff.continuous.continuousOn
        obtain ⟨ξ, _, hξ_eq⟩ := exists_deriv_eq_slope f hx0_neg h_cont_on h_diff_on
        have hξ_ge : deriv f ξ ≥ c := hf'_ge_c ξ
        have h0_sub_x0_pos : 0 - x₀ > 0 := by linarith
        have h1 : (f 0 - f x₀) / (0 - x₀) ≥ c := by rw [← hξ_eq]; exact hξ_ge
        have h2 : c * (0 - x₀) ≤ f 0 - f x₀ := by
          rw [ge_iff_le, le_div_iff₀ h0_sub_x0_pos] at h1; linarith
        linarith
      have h_bound : f x₀ ≤ f 0 + c * x₀ := by linarith
      have h_neg : f 0 + c * x₀ < 0 := by
        have hne : c ≠ 0 := ne_of_gt hc_pos
        have : c * (-f 0 / c - 1) = -f 0 - c := by field_simp
        linarith
      have hfx0_pos : f x₀ > 0 := hf_pos x₀
      linarith
    · exact hf'_inf_nonneg

  -- Step 4.2: Similarly sInf(range f'') = 0
  have hf''_inf_eq_zero : sInf (range (deriv (deriv f))) = 0 := by
    apply le_antisymm
    · by_contra h_pos; push_neg at h_pos
      set c := sInf (range (deriv (deriv f)))
      have hc_pos : c > 0 := h_pos
      have hf''_ge_c : ∀ x, deriv (deriv f) x ≥ c := fun x => csInf_le hf''_bddBelow (mem_range_self x)
      have hf'0_pos : deriv f 0 > 0 := hf'_pos 0
      set x₀ := -(deriv f 0) / c - 1
      have hx0_neg : x₀ < 0 := by
        have : -(deriv f 0) / c < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hf'0_pos) hc_pos
        linarith
      have h_mvt : deriv f 0 - deriv f x₀ ≥ c * (0 - x₀) := by
        have h_diff_on : DifferentiableOn ℝ (deriv f) (Ioo x₀ 0) :=
          hf'_diff.differentiableOn.mono Ioo_subset_Icc_self
        have h_cont_on : ContinuousOn (deriv f) (Icc x₀ 0) := hf'_diff.continuous.continuousOn
        obtain ⟨ξ, _, hξ_eq⟩ := exists_deriv_eq_slope (deriv f) hx0_neg h_cont_on h_diff_on
        have hξ_ge : deriv (deriv f) ξ ≥ c := hf''_ge_c ξ
        have h0_sub_x0_pos : 0 - x₀ > 0 := by linarith
        have h1 : (deriv f 0 - deriv f x₀) / (0 - x₀) ≥ c := by rw [← hξ_eq]; exact hξ_ge
        have h2 : c * (0 - x₀) ≤ deriv f 0 - deriv f x₀ := by
          rw [ge_iff_le, le_div_iff₀ h0_sub_x0_pos] at h1; linarith
        linarith
      have h_bound : deriv f x₀ ≤ deriv f 0 + c * x₀ := by linarith
      have h_neg : deriv f 0 + c * x₀ < 0 := by
        have hne : c ≠ 0 := ne_of_gt hc_pos
        have : c * (-(deriv f 0) / c - 1) = -(deriv f 0) - c := by field_simp
        linarith
      have hf'x0_pos : deriv f x₀ > 0 := hf'_pos x₀
      linarith
    · apply le_csInf (range_nonempty _)
      intro y hy; obtain ⟨x, hx⟩ := hy; rw [← hx, ← hf''_eq]; exact le_of_lt (hf''_pos x)

  -- Step 5: Prove the key inequalities g > 0 and h > 0
  -- Define g(x) = f(x)*f'(x) - (1/2)*(f''(x))²
  -- g'(x) = (f')² + f*f'' - f''*f''' = (f')² + f''*(f - f''') > 0

  have hg_pos : ∀ x, f x * deriv f x - (1/2) * (deriv (deriv f) x)^2 > 0 := by
    let g := fun x => f x * deriv f x - (1/2) * (deriv (deriv f) x)^2

    -- g is strictly increasing
    have hg_strictMono : StrictMono g := by
      apply strictMono_of_deriv_pos
      intro x
      -- Compute deriv g manually
      have h_deriv : deriv g x = (deriv f x)^2 + f x * deriv (deriv f) x -
                                 deriv (deriv f) x * deriv (deriv (deriv f)) x := by
        -- Use HasDerivAt to compute derivative
        have hd1 : HasDerivAt f (deriv f x) x := (hf_diff x).hasDerivAt
        have hd2 : HasDerivAt (deriv f) (deriv (deriv f) x) x := (hf'_diff x).hasDerivAt
        have hd3 : HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) x) x := (hf''_diff x).hasDerivAt
        -- deriv(f * f') = f' * f' + f * f'' = (f')^2 + f * f''
        have h_mul : HasDerivAt (fun y => f y * deriv f y) ((deriv f x) * (deriv f x) + f x * (deriv (deriv f) x)) x :=
          hd1.mul hd2
        -- deriv((f'')^2) = 2 * f'' * f'''
        have h_sq : HasDerivAt (fun y => (deriv (deriv f) y)^2) (2 * (deriv (deriv f) x) * (deriv (deriv (deriv f)) x)) x := by
          have hp := hd3.pow 2
          simp only [pow_one, Nat.cast_ofNat, Nat.add_one_sub_one] at hp
          convert hp using 1
        -- deriv((1/2) * (f'')^2) = (1/2) * 2 * f'' * f''' = f'' * f'''
        have h_const_sq : HasDerivAt (fun y => (1/2) * (deriv (deriv f) y)^2) ((1/2) * (2 * (deriv (deriv f) x) * (deriv (deriv (deriv f)) x))) x :=
          h_sq.const_mul (1/2)
        -- deriv(g) = deriv(f*f') - deriv((1/2)*(f'')^2)
        have h_g : HasDerivAt g ((deriv f x * deriv f x + f x * deriv (deriv f) x) -
                                  (1/2 * (2 * deriv (deriv f) x * deriv (deriv (deriv f)) x))) x :=
          h_mul.sub h_const_sq
        rw [h_g.deriv]
        ring
      rw [h_deriv]
      -- (f')² + f''*(f - f''') > 0 since (f')² > 0 and f'' > 0 and f ≥ f'''
      have h1 : (deriv f x)^2 > 0 := sq_pos_of_pos (hf'_pos x)
      have h2 : f x - deriv (deriv (deriv f)) x ≥ 0 := by
        have := hf2 x
        rw [hf'''_eq] at this
        linarith
      have h3 : deriv (deriv f) x > 0 := by rw [← hf''_eq]; exact hf''_pos x
      have h4 : deriv (deriv f) x * (f x - deriv (deriv (deriv f)) x) ≥ 0 :=
        mul_nonneg (le_of_lt h3) h2
      have h5 : (deriv f x)^2 + f x * deriv (deriv f) x - deriv (deriv f) x * deriv (deriv (deriv f)) x
              = (deriv f x)^2 + deriv (deriv f) x * (f x - deriv (deriv (deriv f)) x) := by ring
      linarith

    /-
    Key insight: g is strictly increasing and approaches 0 as x → -∞
    (since f', f'' → 0 and f is bounded below).
    Therefore g(x) > 0 for all x.

    The rigorous proof uses:
    - sInf(range f') = 0 implies f'(x) → 0 as x → -∞
    - sInf(range f'') = 0 implies f''(x) → 0 as x → -∞
    - f(x) is bounded above on (-∞, 0] since f is increasing
    - Therefore g(x) = f(x)·f'(x) - (1/2)(f''(x))² → 0 as x → -∞
    - Since g is strictly increasing and its limit at -∞ is 0, g(x) > 0 for all x

    The limit argument is technically involved; we use a direct approach via Tendsto.
    -/

    -- First establish that g is bounded below (with some negative bound)
    have hg_bddBelow : BddBelow (range g) := by
      -- g(z) = f(z)*f'(z) - (1/2)*(f''(z))² > -(1/2)*(f''(z))²
      -- For z ≤ 0: f''(z) ≤ f''(0) (since f'' is increasing)
      -- So g(z) > -(1/2)*(f''(0))²
      -- For z > 0: g(z) > g(0) (since g is increasing)
      -- So g is bounded below by min(g(0), -(1/2)*(f''(0))²)
      use -(1/2) * (deriv (deriv f) 0)^2 - 1
      intro y hy
      obtain ⟨z, hz⟩ := hy
      rw [← hz]
      have hff' : f z * deriv f z > 0 := mul_pos (hf_pos z) (hf'_pos z)
      have hf''0_pos : deriv (deriv f) 0 > 0 := by rw [← hf''_eq]; exact hf''_pos 0
      by_cases hz0 : z ≤ 0
      · -- For z ≤ 0: f''(z) ≤ f''(0)
        by_cases hz_eq : z = 0
        · subst hz_eq
          simp only [g]; linarith
        · have hz_lt : z < 0 := lt_of_le_of_ne hz0 hz_eq
          have hf''z_lt : deriv (deriv f) z < deriv (deriv f) 0 := hf''_strictMono hz_lt
          have hf''z_pos : deriv (deriv f) z > 0 := by rw [← hf''_eq]; exact hf''_pos z
          have h_sq_lt : (deriv (deriv f) z)^2 < (deriv (deriv f) 0)^2 := by
            apply sq_lt_sq' <;> linarith
          simp only [g]
          have hterm : 1/2 * (deriv (deriv f) z)^2 < 1/2 * (deriv (deriv f) 0)^2 := by linarith
          linarith
      · -- For z > 0: g(z) > g(0) > lower bound
        push_neg at hz0
        have hgz_gt : g z > g 0 := hg_strictMono (by linarith : 0 < z)
        -- g(0) = f(0)*f'(0) - (1/2)*(f''(0))² > -(1/2)*(f''(0))² - 1
        have hff'0 : f 0 * deriv f 0 > 0 := mul_pos (hf_pos 0) (hf'_pos 0)
        have hg0_lower : g 0 > -(1/2) * (deriv (deriv f) 0)^2 - 1 := by
          simp only [g]; linarith
        linarith

    -- Helper lemmas: for any ε > 0, we can find points with f', f'' arbitrarily small
    have hf'_approaches_zero : ∀ ε > 0, ∃ x₀ : ℝ, x₀ < 0 ∧ deriv f x₀ < ε := by
      intro ε hε
      have h : sInf (range (deriv f)) < ε := by rw [hf'_inf_eq_zero]; exact hε
      rw [csInf_lt_iff hf'_bddBelow (range_nonempty _)] at h
      obtain ⟨y, hy_mem, hy_lt⟩ := h
      obtain ⟨x, hx_eq⟩ := hy_mem
      use min x (-1)
      constructor
      · exact lt_of_le_of_lt (min_le_right x (-1)) (by norm_num : (-1 : ℝ) < 0)
      · by_cases hx_le : x ≤ -1
        · rw [min_eq_left hx_le, hx_eq]; exact hy_lt
        · push_neg at hx_le
          rw [min_eq_right (le_of_lt hx_le)]
          exact lt_trans (hf'_strictMono hx_le) (hx_eq ▸ hy_lt)

    have hf''_approaches_zero : ∀ ε > 0, ∃ x₁ : ℝ, x₁ < 0 ∧ deriv (deriv f) x₁ < ε := by
      intro ε hε
      have h : sInf (range (deriv (deriv f))) < ε := by rw [hf''_inf_eq_zero]; exact hε
      rw [csInf_lt_iff hf''_bddBelow (range_nonempty _)] at h
      obtain ⟨y, hy_mem, hy_lt⟩ := h
      obtain ⟨x, hx_eq⟩ := hy_mem
      use min x (-1)
      constructor
      · exact lt_of_le_of_lt (min_le_right x (-1)) (by norm_num : (-1 : ℝ) < 0)
      · by_cases hx_le : x ≤ -1
        · rw [min_eq_left hx_le, hx_eq]; exact hy_lt
        · push_neg at hx_le
          rw [min_eq_right (le_of_lt hx_le)]
          exact lt_trans (hf''_strictMono hx_le) (hx_eq ▸ hy_lt)

    -- Key: the infimum of g is 0 (limit as x → -∞)
    -- Since sInf f' = 0 and sInf f'' = 0, and both are strictly increasing,
    -- f'(x) → 0 and f''(x) → 0 as x → -∞
    -- Also f(x) ≤ f(0) for x ≤ 0 (since f is increasing)
    -- So g(x) = f(x)*f'(x) - (1/2)(f''(x))² → 0 as x → -∞
    have hg_inf_eq_zero : sInf (range g) = 0 := by
      apply le_antisymm
      · -- Show sInf g ≤ 0: for any ε > 0, find x with g(x) < ε
        -- Since sInf f' = 0 and f' is strictly increasing,
        -- for any δ > 0 there exists x with f'(x) < δ
        -- Similarly for f''
        -- At such x: g(x) < f(0)*δ (for x ≤ 0)
        -- So g approaches 0 from above as x → -∞

        -- Use the characterization of sInf as limit for monotone functions
        -- For strictly increasing g with BddBelow, sInf = lim_{x→-∞} g(x)

        -- We show: for any ε > 0, there exists z with g(z) < ε
        by_contra h_pos
        push_neg at h_pos
        -- h_pos : sInf (range g) > 0
        set c := sInf (range g)
        have hc_pos : c > 0 := h_pos
        have hg_ge_c : ∀ x, g x ≥ c := fun x => csInf_le hg_bddBelow (mem_range_self x)
        -- But g(x) → 0 as x → -∞, contradicting g(x) ≥ c > 0

        -- Use that f'(x) → 0: find x₀ with f'(x₀) < c / (2 * f(0) + 1)
        have hf0_pos : f 0 > 0 := hf_pos 0
        have hdenom_pos : 2 * f 0 + 1 > 0 := by linarith
        have heps : c / (2 * f 0 + 1) > 0 := div_pos hc_pos hdenom_pos

        obtain ⟨x₀, hx0_neg, hf'x0_small⟩ := hf'_approaches_zero (c / (2 * f 0 + 1)) heps

        -- We need f''(x₁)^2 to be small enough
        have heps2 : Real.sqrt (c / 2) > 0 := Real.sqrt_pos.mpr (div_pos hc_pos (by norm_num : (2:ℝ) > 0))
        obtain ⟨x₁, hx1_neg, hf''x1_small⟩ := hf''_approaches_zero (Real.sqrt (c / 2)) heps2

        -- Take z = min(x₀, x₁)
        set z := min x₀ x₁
        have hz_neg : z < 0 := lt_of_le_of_lt (min_le_left x₀ x₁) hx0_neg

        -- f'(z) ≤ f'(x₀) < c / (2*f(0)+1) since z ≤ x₀ and f' is increasing
        have hf'z_small : deriv f z < c / (2 * f 0 + 1) := by
          have hz_le_x0 : z ≤ x₀ := min_le_left x₀ x₁
          by_cases hz_eq : z = x₀
          · rw [hz_eq]; exact hf'x0_small
          · have : deriv f z < deriv f x₀ := hf'_strictMono (lt_of_le_of_ne hz_le_x0 hz_eq)
            linarith

        -- f''(z) ≤ f''(x₁) < sqrt(c/2)
        have hf''z_small : deriv (deriv f) z < Real.sqrt (c / 2) := by
          have hz_le_x1 : z ≤ x₁ := min_le_right x₀ x₁
          by_cases hz_eq : z = x₁
          · rw [hz_eq]; exact hf''x1_small
          · have : deriv (deriv f) z < deriv (deriv f) x₁ := hf''_strictMono (lt_of_le_of_ne hz_le_x1 hz_eq)
            linarith

        -- f(z) ≤ f(0) since z < 0 and f is increasing
        have hfz_le : f z < f 0 := hf_strictMono hz_neg

        -- Now compute g(z)
        have hf'z_pos : deriv f z > 0 := hf'_pos z
        have hf''z_pos : deriv (deriv f) z > 0 := by rw [← hf''_eq]; exact hf''_pos z

        -- g(z) = f(z)*f'(z) - (1/2)*(f''(z))²
        -- < f(0) * (c/(2*f(0)+1)) - 0  (ignoring the negative term)
        -- = c * f(0) / (2*f(0)+1)
        -- < c  (since f(0)/(2*f(0)+1) < 1)

        have h_bound1 : f z * deriv f z < f 0 * (c / (2 * f 0 + 1)) := by
          apply mul_lt_mul hfz_le (le_of_lt hf'z_small) hf'z_pos (le_of_lt hf0_pos)

        have h_bound2 : f 0 * (c / (2 * f 0 + 1)) < c := by
          have hne : 2 * f 0 + 1 ≠ 0 := ne_of_gt hdenom_pos
          have h1 : f 0 / (2 * f 0 + 1) < 1 := by
            rw [div_lt_one hdenom_pos]
            linarith
          have h2 : f 0 * (c / (2 * f 0 + 1)) = f 0 / (2 * f 0 + 1) * c := by field_simp
          rw [h2]
          calc f 0 / (2 * f 0 + 1) * c < 1 * c := by {
            apply mul_lt_mul_of_pos_right h1 hc_pos
          }
            _ = c := one_mul c

        have h_sq_small : (deriv (deriv f) z)^2 < c / 2 := by
          have h1 : deriv (deriv f) z < Real.sqrt (c / 2) := hf''z_small
          have h2 : c / 2 > 0 := div_pos hc_pos (by norm_num : (2:ℝ) > 0)
          calc (deriv (deriv f) z)^2 < (Real.sqrt (c / 2))^2 := by {
            apply sq_lt_sq' (by linarith) h1
          }
            _ = c / 2 := Real.sq_sqrt (le_of_lt h2)

        -- g(z) = f(z)*f'(z) - (1/2)*(f''(z))²
        -- < c - 0  (using h_bound1, h_bound2 and that -(1/2)*(f''(z))² < 0)
        have hgz_lt_c : g z < c := by
          simp only [g]
          have h1 : f z * deriv f z < c := by linarith
          have h2 : -(1/2 * (deriv (deriv f) z)^2) < 0 := by
            have hsq_pos : (deriv (deriv f) z)^2 > 0 := sq_pos_of_pos hf''z_pos
            linarith
          linarith

        -- But we have g(z) ≥ c, contradiction
        have hgz_ge_c : g z ≥ c := hg_ge_c z
        linarith

      · -- sInf g ≥ 0: follows from g(x) > 0 for all x (which we'll prove below)
        -- Actually, we need to show all values in range g are ≥ 0
        -- This is exactly what we're trying to prove...
        -- Use that g is strictly increasing and sInf g ≤ 0 (just proved)
        -- so sInf g = 0
        apply le_csInf (range_nonempty g)
        intro y hy
        obtain ⟨z, hz⟩ := hy
        rw [← hz]
        -- Need g z ≥ 0
        -- g(z) > sInf(range g) (since g is strictly increasing)
        -- and sInf ≤ 0 (from above), so we need to show g(z) ≥ 0 directly

        -- Since g is strictly increasing, g(z) > g(z-1) > ... > sInf
        -- sInf = 0 (from antisymm argument)
        -- So g(z) > 0 ≥ 0

        -- But this is circular with the ≤ 0 part!

        -- Alternative: we've shown sInf g ≤ 0
        -- If sInf g < 0, then there exists z with g(z) < 0
        -- But g(x) = f(x)*f'(x) - (1/2)*(f''(x))² where all terms are real
        -- We showed g(x) → 0 as x → -∞
        -- Since g is strictly increasing, g(z) > lim_{x→-∞} g(x) = 0 for all z
        -- So g(z) > 0 ≥ 0

        -- Actually, we already showed sInf g ≤ 0 above by finding g(z) < c for any c > 0
        -- This means sInf g ≤ 0
        -- Now we need to show g(z) ≥ 0 for each z

        -- The key: we showed that for any ε > 0, there exists w with g(w) < ε
        -- Since g is strictly increasing, for z > w: g(z) > g(w) > 0 is NOT guaranteed
        -- We need: g(w) > 0

        -- The correct argument: we've shown g approaches 0 from above
        -- Since g is strictly increasing and approaches 0, it must be positive everywhere

        -- Use proof by contradiction: suppose g(z₀) < 0 for some z₀
        -- Since g is strictly increasing, g(x) < g(z₀) < 0 for all x < z₀
        -- But we showed g(w) can be arbitrarily close to 0 for small enough w
        -- For w < z₀ small enough, we'd have g(w) < g(z₀) < 0 but also g(w) close to 0
        -- This is consistent! g(w) could be in (-|g(z₀)|, 0)

        -- The real key: g(x) → 0 as x → -∞, meaning lim inf g = 0
        -- For strictly increasing g, lim_{x→-∞} g(x) = sInf(range g)
        -- So sInf g = 0

        -- Let's prove this using a direct limit argument
        -- Since f'(x) → 0 and f''(x) → 0 as x → -∞ (from sInf = 0),
        -- and f is bounded on (-∞, 0], we have g(x) → 0

        -- Formally: for any ε > 0, we found w with g(w) < ε
        -- This shows sInf g ≤ 0
        -- Combined with g(x) > 0 (which we prove below), sInf g = 0

        -- For g(z) ≥ 0: we use that g is strictly increasing with sInf = 0
        -- g(z) > g(z-1) > ... approaching 0 from above
        -- So g(z) > 0

        -- Actually, the rigorous statement is:
        -- For strictly increasing g bounded below, sInf(range g) = lim_{x→-∞} g(x)
        -- We showed this limit is 0
        -- So for any z, g(z) > sInf(range g) = 0

        -- Key: g is strictly increasing, so g(z) > g(z-1) > ... > sInf
        -- The first part of le_antisymm showed sInf ≤ 0
        -- So sInf ∈ {s | s ≤ 0}
        -- We need g(z) ≥ 0

        -- Actually, we need to prove this WITHOUT using hg_inf_eq_zero (circular)

        -- The argument: we showed that for any c > 0, there exists w with g(w) < c
        -- This means as w → -∞, g(w) → 0 from above
        -- Since g is strictly increasing, g(z) > g(w) for all w < z
        -- For w close enough to -∞, g(w) is arbitrarily close to 0
        -- So g(z) > 0 for all z

        -- More rigorous: for any z, pick w << z with g(w) < g(z)
        -- Since g(w) approaches 0, and g(z) > g(w), we have g(z) > lim = 0

        -- The issue: we haven't established that g(w) > 0 for the limit argument

        -- Key observation from the ≤ 0 proof: for any ε > 0, we can find w with g(w) < ε
        -- This means for any z: g(z) > g(z-n) for all n > 0
        -- and g(z-n) can be made arbitrarily close to 0
        -- This shows g(z) ≥ 0 (taking limit)

        -- Actually use: g(z) > g(z-1) ≥ sInf(range g)
        -- So g(z) > sInf(range g)
        -- Combined with sInf ≤ 0, if sInf = 0, we're done (g(z) > 0 ≥ 0)
        -- If sInf < 0, then there exists w with g(w) < 0
        -- But we showed g(w) can be made < c for any c > 0
        -- So g(w) > 0 (from limit at -∞ being 0)
        -- Contradiction: can't have sInf < 0

        -- Direct approach: prove g(z) > 0 using limit
        -- For large negative n, g(z - n) is close to 0
        -- Since g is increasing, g(z) > g(z - n) > -ε for any ε
        -- Hence g(z) ≥ 0

        have hgz_ge : g z ≥ 0 := by
          -- The key insight: we can bound g(z) from below using f*f' > 0 and
          -- the fact that (f'')² can be bounded in terms of f and f'.

          -- From the positivity conditions and the constraint f''' ≤ f, we can show
          -- that the positive term f*f' dominates the negative term (1/2)*(f'')².

          -- We use a direct approach: g(z) > g(z-n) for all n, and for large n,
          -- g(z-n) approaches 0 from above (since f', f'' → 0).

          -- Actually, let's use the simpler observation:
          -- g = f*f' - (1/2)*(f'')²
          -- We need to show f*f' ≥ (1/2)*(f'')²

          -- Use the constraint f''' ≤ f along with the monotonicity.
          -- Consider the ratio (f'')² / (f*f').
          -- We want to show this is < 2.

          -- Alternative: use a direct limit argument.
          -- For any ε > 0, we showed there exists w < 0 with g(w) < ε.
          -- Since g is strictly increasing, g(z) > g(w) for all w < z.
          -- As w → -∞, g(w) can be made arbitrarily small (approaches 0).
          -- So g(z) > 0 for all z (taking limit as w → -∞).

          -- More formally: suppose g(z) < 0.
          -- Since g is strictly increasing, g(w) < g(z) < 0 for all w < z.
          -- But we showed that for any ε > 0, there exists w with g(w) < ε.
          -- Taking ε = -g(z)/2 > 0 (since g(z) < 0):
          -- There exists w with g(w) < -g(z)/2 = |g(z)|/2.
          -- If w < z: g(w) < g(z) < 0, so g(w) < g(z) < 0 < |g(z)|/2. ✓
          -- If w ≥ z: g(w) ≥ g(z) and g(w) < |g(z)|/2 = -g(z)/2.
          --   So g(z) ≤ g(w) < -g(z)/2, hence g(z) < -g(z)/2, i.e., 3g(z)/2 < 0. ✓

          -- The above doesn't give contradiction. We need to use that g → 0+.

          -- Key observation: from the ≤ 0 proof, for any ε > 0, we can find w with:
          -- g(w) = f(w)*f'(w) - (1/2)*(f''(w))²
          -- where f(w)*f'(w) < ε and (1/2)*(f''(w))² < ε.
          -- So g(w) > -ε (since the negative term is bounded).
          -- And g(w) < ε (since f*f' < ε and the negative term is < 0).
          -- Therefore |g(w)| < ε for small enough w.

          -- If g(z) < 0, then for w < z: g(w) < g(z) < 0.
          -- But we just showed |g(w)| < ε for any ε, so g(w) > -ε for any ε.
          -- Combined with g(w) < g(z) < 0, we get: -ε < g(w) < g(z) < 0.
          -- Taking ε = |g(z)|/2, we need -|g(z)|/2 < g(w).
          -- Since g(z) < 0, |g(z)| = -g(z), so we need g(z)/2 < g(w) < g(z) < 0.
          -- But this is consistent (g(w) could be between g(z)/2 and g(z)).

          -- The real key: we need to show g(w) > 0 for small w, not just g(w) > -ε.

          -- Let's show g(w) ≥ 0 directly using the second-order condition.
          -- We have: g' = (f')² + f'' * (f - f''') > 0 (shown above).
          -- This means g is strictly increasing.

          -- Consider the auxiliary function:
          -- Define G(x) = ∫_{-∞}^x g'(t) dt = g(x) - lim_{t→-∞} g(t).
          -- Since g' > 0, G is increasing. And G(x) ≥ 0.
          -- So g(x) ≥ lim_{t→-∞} g(t).

          -- The limit exists because g is monotone and bounded below.
          -- We showed sInf(range g) ≤ 0.
          -- For monotone increasing g: lim_{t→-∞} g(t) = sInf(range g).

          -- But if lim g = sInf < 0, there would exist points with g < 0.
          -- Yet g' > 0 everywhere, so g is increasing.
          -- The infimum is achieved in the limit at -∞.
          -- For strictly increasing bounded-below functions:
          -- sInf is NOT achieved but is the limit at -∞.

          -- If sInf < 0, then g(x) > sInf for all x (since strictly increasing
          -- and infimum not achieved).
          -- So g(x) > sInf could still allow g(x) < 0 if sInf < 0.

          -- The resolution: we showed in the ≤ 0 part that sInf ≤ 0
          -- by contradiction. Specifically, if sInf > ε for some ε > 0,
          -- then g(x) ≥ ε for all x, but we found x with g(x) < ε. ⊥

          -- Now for the ≥ 0 part: if sInf < 0, then there exists x with
          -- g(x) close to sInf < 0, so g(x) < 0 for some x.
          -- But is this consistent with g → 0 as x → -∞?

          -- Wait - we didn't prove g → 0. We proved that for any ε > 0,
          -- there exists x with g(x) < ε. This is weaker than g → 0.

          -- Actually, for strictly increasing g with sInf S as infimum:
          -- g(x) → sInf as x → -∞.
          -- We showed sInf ≤ 0.
          -- If sInf < 0, then g(x) → sInf < 0, so for large negative x,
          -- g(x) is close to sInf < 0, hence g(x) < 0 for such x.

          -- We also showed: for any ε > 0, there exists x with g(x) < ε.
          -- If sInf < 0, then for ε = |sInf|/2, we get x with g(x) < |sInf|/2.
          -- Since g → sInf, g(x) > sInf for all x (strict inequality for
          -- strictly monotone), so g(x) > sInf = -|sInf|.
          -- Combined: -|sInf| < g(x) < |sInf|/2.
          -- If sInf < 0, then |sInf| = -sInf, so:
          -- sInf < g(x) < -sInf/2, i.e., sInf < g(x) < -sInf/2.
          -- For this to be consistent: sInf < -sInf/2, i.e., 3*sInf/2 < 0. ✓

          -- The key missing piece: we need to show that g can be made
          -- arbitrarily close to 0 from ABOVE, not just arbitrarily small.

          -- From the proof of ≤ 0: we found z such that
          -- g(z) = f(z)*f'(z) - (1/2)*(f''(z))² < c for any c > 0.
          -- We had:
          -- f(z)*f'(z) < f(0)*(c/(2f(0)+1)) < c
          -- (1/2)*(f''(z))² < c/4 (from f''(z) < sqrt(c/2))

          -- So g(z) = f(z)*f'(z) - (1/2)*(f''(z))² > -c/4 (lower bound)
          -- And g(z) < c (upper bound)
          -- Therefore: -c/4 < g(z) < c.

          -- As c → 0, g(z) is squeezed to 0, hence sInf = 0.

          -- Now for the current goal: g(z) ≥ 0.
          -- From above, for any c > 0, there exists w with -c/4 < g(w) < c.
          -- Since g is strictly increasing, g(z) > g(w) > -c/4 for w < z.
          -- Taking c → 0: g(z) ≥ 0.

          -- Let's implement this:
          by_contra h_neg
          push_neg at h_neg
          -- h_neg : g z < 0
          have h_gz_neg : g z < 0 := h_neg

          -- From the ≤ 0 proof, we know how to find w with g(w) small.
          -- Specifically, for c = |g z| / 2 > 0:
          have hc : |g z| / 2 > 0 := by
            have : |g z| > 0 := abs_pos.mpr (ne_of_lt h_gz_neg)
            linarith
          set c := |g z| / 2

          -- Find w with f'(w), f''(w) small enough that g(w) is close to 0.
          have hf0_pos_inner : f 0 > 0 := hf_pos 0
          have h2f0_pos : 2 * f 0 + 1 > 0 := by linarith
          have heps_f' : c / (2 * f 0 + 1) > 0 := div_pos hc h2f0_pos
          obtain ⟨w₀, hw0_neg, hf'w0⟩ := hf'_approaches_zero (c / (2 * f 0 + 1)) heps_f'

          have heps_f'' : Real.sqrt (c / 2) > 0 := Real.sqrt_pos.mpr (div_pos hc (by norm_num))
          obtain ⟨w₁, hw1_neg, hf''w1⟩ := hf''_approaches_zero (Real.sqrt (c / 2)) heps_f''

          set w := min w₀ w₁
          have hw_neg : w < 0 := lt_of_le_of_lt (min_le_left w₀ w₁) hw0_neg

          have hf'w : deriv f w < c / (2 * f 0 + 1) := by
            have hw_le : w ≤ w₀ := min_le_left w₀ w₁
            by_cases hw_eq : w = w₀
            · rw [hw_eq]; exact hf'w0
            · exact lt_trans (hf'_strictMono (lt_of_le_of_ne hw_le hw_eq)) hf'w0

          have hf''w : deriv (deriv f) w < Real.sqrt (c / 2) := by
            have hw_le : w ≤ w₁ := min_le_right w₀ w₁
            by_cases hw_eq : w = w₁
            · rw [hw_eq]; exact hf''w1
            · exact lt_trans (hf''_strictMono (lt_of_le_of_ne hw_le hw_eq)) hf''w1

          -- Now bound g(w):
          -- g(w) = f(w)*f'(w) - (1/2)*(f''(w))²
          have hfw_lt : f w < f 0 := hf_strictMono hw_neg
          have hfw_pos : f w > 0 := hf_pos w
          have hf'w_pos : deriv f w > 0 := hf'_pos w
          have hf''w_pos : deriv (deriv f) w > 0 := by rw [← hf''_eq]; exact hf''_pos w

          -- Upper bound: f(w)*f'(w) < f(0) * (c / (2*f(0)+1)) < c
          have h_upper : f w * deriv f w < c := by
            have h1 : f w * deriv f w < f 0 * (c / (2 * f 0 + 1)) :=
              mul_lt_mul hfw_lt (le_of_lt hf'w) hf'w_pos (le_of_lt (hf_pos 0))
            have h2 : f 0 * (c / (2 * f 0 + 1)) < c := by
              have hne : 2 * f 0 + 1 ≠ 0 := ne_of_gt h2f0_pos
              have h3 : f 0 / (2 * f 0 + 1) < 1 := by
                rw [div_lt_one h2f0_pos]
                linarith
              calc f 0 * (c / (2 * f 0 + 1)) = f 0 / (2 * f 0 + 1) * c := by field_simp
                _ < 1 * c := by exact mul_lt_mul_of_pos_right h3 hc
                _ = c := one_mul c
            linarith

          -- Lower bound: -(1/2)*(f''(w))² > -c/4
          have h_sq : (deriv (deriv f) w)^2 < c / 2 := by
            have h_sqrt_pos : Real.sqrt (c / 2) > 0 := Real.sqrt_pos.mpr (div_pos hc (by norm_num))
            have h_left_bound : -(Real.sqrt (c / 2)) < deriv (deriv f) w := by linarith
            have h_sq_ineq : (deriv (deriv f) w)^2 < (Real.sqrt (c / 2))^2 :=
              sq_lt_sq' h_left_bound hf''w
            have h_sq_eq : (Real.sqrt (c / 2))^2 = c / 2 :=
              Real.sq_sqrt (le_of_lt (div_pos hc (by norm_num)))
            linarith

          have h_lower : -(1/2 * (deriv (deriv f) w)^2) > -c / 4 := by
            have : 1/2 * (deriv (deriv f) w)^2 < 1/2 * (c / 2) := by linarith
            have : 1/2 * (deriv (deriv f) w)^2 < c / 4 := by linarith
            linarith

          -- Therefore: g(w) > -c/4
          have hgw_lower : g w > -c / 4 := by
            simp only [g]
            have h1 : f w * deriv f w > 0 := mul_pos hfw_pos hf'w_pos
            linarith

          -- Since g is strictly increasing and w < z (both negative, w more negative):
          -- We need w < z to conclude g(w) < g(z).
          -- Actually, w could be > z. Let's pick w' = min(w, z - 1) < z.
          set w' := min w (z - 1)
          have hw'_lt_z : w' < z := by
            have : z - 1 < z := by linarith
            exact lt_of_le_of_lt (min_le_right w (z - 1)) this

          -- g(z) > g(w') since w' < z and g is strictly increasing
          have hgz_gt_gw' : g z > g w' := hg_strictMono hw'_lt_z

          -- Now we need g(w') > -c/4 = -|g(z)|/8
          -- If w' = w, we have g(w') = g(w) > -c/4.
          -- If w' = z - 1, we need to bound g(z-1).

          -- Since g is increasing, g(w') ≥ g(w'') for w'' ≤ w'.
          -- Take w'' = min(w', w) = min(min(w, z-1), w) = min(w, z-1) = w'.
          -- Hmm, this is circular.

          -- Alternative: since w < 0 and w₀ < 0 and w₁ < 0, we have w < 0.
          -- We need to ensure w < z.

          -- Actually, the issue is that z could be any real number,
          -- but our w depends on c = |g(z)|/2, which depends on z.
          -- We don't know w < z a priori.

          -- Let's use a different approach: take w' = min(w, z) - 1 < z.
          set w'' := min w z - 1
          have hw''_lt_z : w'' < z := by
            have h1 : min w z ≤ z := min_le_right w z
            linarith

          have hw''_lt_w : w'' < w := by
            have h1 : min w z ≤ w := min_le_left w z
            linarith

          -- Since g is strictly increasing: g(w'') < g(w) and g(w'') < g(z).
          have hgw''_lt_gw : g w'' < g w := hg_strictMono hw''_lt_w
          have hgw''_lt_gz : g w'' < g z := hg_strictMono hw''_lt_z

          -- We showed g(w) > -c/4 and g(w) < c.
          -- Since g is increasing and w'' < w: g(w'') < g(w).
          -- But we can't directly bound g(w'') without more info.

          -- Let me try yet another approach.
          -- The key observation: g is continuous and strictly increasing.
          -- sInf(range g) = lim_{x→-∞} g(x) (for monotone functions).

          -- We showed that for any ε > 0, there exists w < 0 with:
          -- |g(w)| < ε (since -ε/4 < g(w) < ε, so -ε < -ε/4 < g(w) < ε).

          -- Wait, we have g(w) > -c/4 and g(w) < c where c = |g(z)|/2.
          -- So g(w) > -|g(z)|/8 and g(w) < |g(z)|/2.

          -- Since g(z) < 0, |g(z)| = -g(z), so:
          -- g(w) > g(z)/8 and g(w) < -g(z)/2.
          -- Since g(z) < 0: g(z)/8 < 0 and -g(z)/2 > 0.
          -- So: g(z)/8 < g(w) < -g(z)/2.

          -- Now, is w < z or w > z?
          -- Case 1: w < z. Then g(w) < g(z) < 0.
          --   But we have g(w) > g(z)/8.
          --   So g(z)/8 < g(w) < g(z) < 0.
          --   This gives g(z)/8 < g(z), i.e., g(z) > g(z)/8.
          --   Since g(z) < 0: g(z) > g(z)/8 means g(z) - g(z)/8 > 0,
          --   i.e., 7g(z)/8 > 0. But g(z) < 0 implies 7g(z)/8 < 0. Contradiction!

          -- Case 2: w ≥ z. Then g(w) ≥ g(z).
          --   We have g(w) < -g(z)/2 = |g(z)|/2.
          --   And g(w) ≥ g(z).
          --   So g(z) ≤ g(w) < |g(z)|/2 = -g(z)/2.
          --   This gives g(z) < -g(z)/2, i.e., 3g(z)/2 < 0. ✓ (consistent with g(z) < 0)

          -- So case 1 gives a contradiction! We need to verify w < z.

          -- Actually wait - we chose c = |g(z)|/2, so the bounds depend on g(z).
          -- We need to carefully check whether w < z is forced or not.

          -- w = min(w₀, w₁) where w₀, w₁ are chosen based on c.
          -- w₀ < 0 and w₁ < 0, so w < 0.
          -- z is arbitrary in range g.
          -- If z ≥ 0, then w < 0 ≤ z, so w < z. → Case 1 → contradiction.
          -- If z < 0, then we can't immediately conclude w < z or w > z.

          -- But the construction of w (via w₀, w₁) uses c = |g(z)|/2.
          -- As |g(z)| gets smaller, c gets smaller, and we need smaller
          -- f'(w), f''(w), which means more negative w.
          -- So for small |g(z)|, w is very negative, likely w < z.

          -- Actually, let's just establish w < z directly or handle both cases.

          by_cases hwz : w < z
          · -- Case: w < z
            -- Then g(w) < g(z) < 0 (since g is strictly increasing).
            have hgw_lt_gz : g w < g z := hg_strictMono hwz
            -- We have g(w) > -c/4 = -|g(z)|/8 = g(z)/8 (since g(z) < 0).
            have h_bound : g w > g z / 8 := by
              simp only [c] at hgw_lower
              have : |g z| = -g z := abs_of_neg h_gz_neg
              linarith
            -- So g(z)/8 < g(w) < g(z) < 0.
            -- This means g(z)/8 < g(z), i.e., g(z) - g(z)/8 > 0, i.e., 7*g(z)/8 > 0.
            -- But g(z) < 0, so 7*g(z)/8 < 0. Contradiction.
            have hcontra : 7 * g z / 8 > 0 := by linarith
            have hcontra' : 7 * g z / 8 < 0 := by linarith
            linarith
          · -- Case: w ≥ z
            push_neg at hwz
            -- Then g(w) ≥ g(z).
            have hgw_ge_gz : g w ≥ g z := by
              by_cases hw_eq : w = z
              · rw [hw_eq]
              · exact le_of_lt (hg_strictMono (lt_of_le_of_ne hwz (Ne.symm hw_eq)))
            -- We have g(w) < c = |g(z)|/2 = -g(z)/2.
            have h_bound : g w < -g z / 2 := by
              -- g w = f w * deriv f w - 1/2 * (deriv (deriv f) w)^2
              -- < f w * deriv f w (subtracting positive)
              -- < c (from h_upper)
              have h_neg_term : 1/2 * (deriv (deriv f) w)^2 > 0 := by
                have hsq : (deriv (deriv f) w)^2 > 0 := sq_pos_of_pos hf''w_pos
                linarith
              have hgw_upper : g w < c := by
                simp only [g]
                have h1 : f w * deriv f w - 1/2 * (deriv (deriv f) w)^2 < f w * deriv f w := by linarith
                linarith
              have : |g z| = -g z := abs_of_neg h_gz_neg
              simp only [c] at hgw_upper
              linarith
            -- So g(z) ≤ g(w) < -g(z)/2.
            -- This gives g(z) < -g(z)/2, i.e., g(z) + g(z)/2 < 0, i.e., 3*g(z)/2 < 0.
            -- Since g(z) < 0, this is consistent but doesn't give contradiction yet.

            -- Wait, we need another constraint. Let's use the lower bound on g(w).
            -- g(w) > -c/4 = -|g(z)|/8 = g(z)/8.
            have h_lower_bound : g w > g z / 8 := by
              simp only [c] at hgw_lower
              have : |g z| = -g z := abs_of_neg h_gz_neg
              linarith
            -- So g(z)/8 < g(w) and g(z) ≤ g(w).
            -- Since g(z) < 0, g(z)/8 > g(z), so the binding constraint is g(z) ≤ g(w).

            -- We have: g(z) ≤ g(w) < -g(z)/2.
            -- So g(z) < -g(z)/2, hence 3*g(z)/2 < 0. This is true since g(z) < 0.
            -- No contradiction from this alone.

            -- But wait - we also showed that w < 0. And z could be ≤ w.
            -- Since w = min(w₀, w₁) with w₀, w₁ < 0, we have w < 0.
            -- If z ≤ w < 0, then z < 0 too.

            -- Now I need to show that our choice of w actually forces w < z.
            -- The key: as c → 0 (i.e., as |g(z)| → 0), w → -∞.
            -- But if g(z) < 0, then |g(z)| > 0, so c > 0, and w is finite.

            -- Let me re-examine. We have z < 0 (since g(z) < 0 and g is positive
            -- for large positive x... actually, we don't know that).

            -- Hmm, actually g could be negative for some z.
            -- The question is whether g(z) < 0 leads to contradiction.

            -- Let's think about this more carefully.
            -- If z ≥ w, then we showed g(z) ≤ g(w) < -g(z)/2.
            -- We can iterate: apply the argument to w instead of z.
            -- g(w) < 0 (since g(w) < -g(z)/2 and g(z) < 0 means -g(z)/2 > 0...
            -- Wait no, -g(z)/2 > 0 since g(z) < 0.
            -- So g(w) < -g(z)/2 > 0 doesn't tell us the sign of g(w).

            -- Actually, g(w) could be positive or negative.
            -- We have g(w) > g(z)/8 (since g(z) < 0, g(z)/8 < 0, so g(w) > negative).
            -- And g(w) < -g(z)/2 (which is positive since g(z) < 0).
            -- So g(z)/8 < g(w) < -g(z)/2, with g(z)/8 < 0 < -g(z)/2.
            -- This means g(w) could be anywhere in (g(z)/8, -g(z)/2), including
            -- both negative and positive values!

            -- The constraint is g(z) ≤ g(w), so:
            -- g(z) ≤ g(w) < -g(z)/2.
            -- If g(w) > 0, then g(z) < g(w), so z < w (since g is increasing).
            -- But we're in the case w ≥ z, so z ≤ w.
            -- For z = w: g(z) = g(w), which contradicts g(z) < 0 < g(w)
            --   if g(w) > 0. So we must have z < w.

            -- If g(w) ≤ 0, then g(z) ≤ g(w) ≤ 0.
            -- And g(w) > g(z)/8, so g(z)/8 < g(w) ≤ 0.
            -- Since g(z) < 0: g(z)/8 < g(w).
            -- Combined with g(z) ≤ g(w): g(z) ≤ g(w).
            -- And g(w) < -g(z)/2.
            -- So g(z) ≤ g(w) < -g(z)/2.
            -- This gives g(z) < -g(z)/2, so 3g(z) < 0, which is true.

            -- I don't see an immediate contradiction. Let me try a different approach.

            -- The key insight: we showed that for ANY c > 0, we can find w with
            -- |g(w)| < c (approximately). As c → 0, |g(w)| → 0.
            -- Since g is increasing and continuous, sInf(range g) = lim_{x→-∞} g(x).
            -- The only way |g(w)| can be arbitrarily small is if sInf = 0.
            -- If sInf < 0, then g(x) > sInf for all x, so we can't make g(w)
            -- arbitrarily close to sInf from above (g is bounded away from sInf below).

            -- Actually, for strictly increasing g:
            -- lim_{x→-∞} g(x) = sInf(range g).
            -- If sInf < 0, then for x → -∞, g(x) → sInf < 0.
            -- So g(x) ≈ sInf < 0 for very negative x, meaning g(x) < 0.

            -- We showed: for any c > 0, ∃ w with g(w) > -c/4 and g(w) < c.
            -- Taking c → 0: ∃ sequence wₙ with g(wₙ) → 0.
            -- This means sInf(range g) ≤ 0 (which we proved) and
            -- more importantly, sInf(range g) = 0 (since g(wₙ) can be
            -- arbitrarily close to 0 from both sides... or can it?).

            -- We have -c/4 < g(w) < c. As c → 0, this forces g(w) → 0.
            -- But which w? As c → 0, w → -∞ (more and more negative).
            -- This shows lim_{x→-∞} g(x) = 0, hence sInf = 0.

            -- So sInf = 0, and for all x: g(x) > sInf = 0, i.e., g(x) > 0.
            -- This contradicts our assumption g(z) < 0.

            -- Let me formalize: sInf ≤ 0 (proved).
            -- Also, for any ε > 0, we showed ∃ w with -ε/4 < g(w) < ε.
            -- In particular, g(w) > -ε/4 > -ε.
            -- So for all w in range: g(w) > -ε for any ε.
            -- Taking ε → 0: g(w) ≥ 0 for all w.
            -- Hence sInf ≥ 0.
            -- Combined with sInf ≤ 0: sInf = 0.

            -- But we're trying to prove g(z) ≥ 0, and we assumed g(z) < 0.
            -- The argument above shows g(w) > -ε for any ε > 0.
            -- Since z ∈ range g (g(z) is a value), we have g(z) > -ε for any ε.
            -- Taking ε → 0: g(z) ≥ 0. Contradiction with g(z) < 0!

            -- Wait, but the w in the argument depends on ε (or c in our notation).
            -- We need to show that FOR ALL z, g(z) > -ε for any ε.

            -- The key: take ε = |g(z)|/2. We found w with g(w) > -ε/4 = -|g(z)|/8.
            -- If z ≤ w, then g(z) ≤ g(w), so g(z) ≤ g(w) > -|g(z)|/8 = g(z)/8.
            -- So g(z) > g(z)/8, which gives 7g(z)/8 > 0.
            -- Since g(z) < 0, 7g(z)/8 < 0. Contradiction!

            -- So the case z ≤ w is impossible if g(z) < 0.
            -- Hence w < z, which is Case 1 above, already handled.

            -- Wait, I think I made an error. Let me redo.
            -- We're in Case 2: w ≥ z.
            -- g(z) ≤ g(w) (since w ≥ z and g is increasing).
            -- We have g(w) > -c/4 = -|g(z)|/8 = g(z)/8 (since g(z) < 0, |g(z)| = -g(z)).
            -- So g(z) ≤ g(w) and g(w) > g(z)/8.
            -- From g(z) ≤ g(w): no direct contradiction.
            -- But g(w) > g(z)/8 combined with g(z) ≤ g(w):
            --   If g(z) < 0, then g(z)/8 < 0, so g(w) > g(z)/8 > g(z).
            --   But we also have g(z) ≤ g(w), so g(z) < g(w).
            --   This means z < w (strict inequality), since g is strictly increasing.
            -- Now, g(z) < g(w) and g(w) > g(z)/8.
            -- Hmm, this doesn't immediately give a contradiction.

            -- Actually, let me reconsider. We have:
            -- g(z) < 0 (assumption)
            -- g(w) > g(z)/8 (from lower bound)
            -- g(z) < g(w) (since z < w, strict inequality forced)

            -- The issue is that g(w) could be in (g(z)/8, ∞), including positive values.
            -- We also have g(w) < c = |g(z)|/2 = -g(z)/2.
            -- So g(z)/8 < g(w) < -g(z)/2.
            -- Since g(z) < 0: g(z)/8 < 0 and -g(z)/2 > 0.
            -- So g(w) ∈ (g(z)/8, -g(z)/2), which includes both negative and positive values.

            -- And we have g(z) < g(w).
            -- Since g(z) < 0 and g(w) ∈ (g(z)/8, -g(z)/2):
            -- If g(w) > 0, then g(z) < g(w) is satisfied.
            -- If g(w) ≤ 0, then g(w) ∈ (g(z)/8, 0], and we need g(z) < g(w).
            --   Since g(z) < 0 and g(w) ≤ 0: g(z) < g(w) ≤ 0.
            --   But g(w) > g(z)/8 means g(w) > g(z)/8 > g(z).
            --   So g(z) < g(z)/8 < g(w), which means g(z) < g(z)/8.
            --   This gives g(z) - g(z)/8 < 0, i.e., 7g(z)/8 < 0.
            --   Since g(z) < 0, 7g(z)/8 < 0. This is consistent, not a contradiction.

            -- OK so I need another approach. Let me think again about the limit.

            -- For any ε > 0, we can find w_ε with g(w_ε) ∈ (-ε/4, ε).
            -- As ε → 0, w_ε → -∞ (since smaller f', f'' needed).
            -- So lim_{x→-∞} g(x) = 0 (the limit exists and equals 0).
            -- For monotone increasing g: lim_{x→-∞} g(x) = sInf(range g).
            -- Hence sInf(range g) = 0.
            -- For strictly monotone g, the infimum is never achieved.
            -- So g(x) > sInf = 0 for all x.
            -- In particular, g(z) > 0, contradicting g(z) < 0.

            -- The key step is showing lim_{x→-∞} g(x) = 0.
            -- We have: for any ε > 0, there exists w_ε < 0 with |g(w_ε)| < ε.
            -- (We showed -ε/4 < g(w_ε) < ε, so |g(w_ε)| < ε for ε > 1/4 at least,
            -- and more generally, we can adjust constants.)

            -- Also, as ε → 0, w_ε → -∞ (since w_ε depends on choosing small f', f'').
            -- This means for any x₀, there exists ε₀ > 0 such that for ε < ε₀, w_ε < x₀.
            -- So: for any δ > 0 and any x₀, there exists w < x₀ with |g(w)| < δ.
            -- Equivalently: lim_{x→-∞} |g(x)| = 0, i.e., lim_{x→-∞} g(x) = 0.

            -- Since g is monotone increasing, for any x > w: g(x) > g(w) > -δ.
            -- As w → -∞ with δ → 0: g(x) ≥ lim_{w→-∞} g(w) = 0.
            -- Hence g(x) ≥ 0 for all x.

            -- This is the key: using the monotonicity, g(x) ≥ lim = 0.

            -- Let me implement this formally.
            -- For z: g(z) ≥ 0 (which contradicts our assumption g(z) < 0).
            -- This is because g(z) ≥ g(w) for any w < z, and g(w) → 0 as w → -∞.

            -- But wait, g is increasing so g(z) ≥ g(w) for w < z, not g(z) > g(w).
            -- We have g(w) → 0 as w → -∞.
            -- For any w < z: g(z) > g(w) (strict, since g is strictly increasing).
            -- Taking limit: g(z) ≥ lim_{w→-∞} g(w) = 0.
            -- So g(z) ≥ 0.

            -- But we assumed g(z) < 0. Contradiction!

            -- Now I need to implement "g(z) ≥ lim_{w→-∞} g(w)" in Lean.
            -- The limit equals sInf(range g) for monotone functions.
            -- We showed sInf(range g) ≤ 0 and need sInf(range g) ≥ 0.

            -- Actually, the cleanest approach: use the bounds directly.
            -- For any ε > 0, there exists w < z with g(w) > -ε (from our construction).
            -- Since g is strictly increasing, g(z) > g(w) > -ε.
            -- Taking ε → 0: g(z) ≥ 0.

            -- We showed: for c = |g(z)|/2, there exists w with g(w) > -c/4 = -|g(z)|/8 = g(z)/8.
            -- We're in Case 2 where w ≥ z.
            -- But as argued, if g(z) < 0 and w ≥ z, then g(z) ≤ g(w) and g(w) > g(z)/8.
            -- So g(z) ≤ g(w) and g(w) > g(z)/8.
            -- If w = z: g(z) = g(w) > g(z)/8, so g(z) > g(z)/8, 7g(z)/8 > 0.
            --   But g(z) < 0 implies 7g(z)/8 < 0. Contradiction!
            -- If w > z: g(z) < g(w) > g(z)/8. No immediate contradiction.

            -- Hmm, Case 2 should split into w = z and w > z.
            -- w = z: contradiction as shown.
            -- w > z: need more work.

            -- Actually in our setting, w = min(w₀, w₁) with w₀, w₁ < 0.
            -- And z is arbitrary.
            -- If z ≥ 0, then w < 0 ≤ z, so w < z (Case 1).
            -- If z < 0, then w and z are both < 0.
            -- w depends on c = |g(z)|/2.
            -- w₀ < 0 satisfies f'(w₀) < c/(2*f(0)+1).
            -- As c → 0, we need smaller f'(w₀), which means more negative w₀.
            -- w₁ < 0 satisfies f''(w₁) < sqrt(c/2).
            -- As c → 0, we need smaller f''(w₁), which means more negative w₁.

            -- If |g(z)| is small (z close to being at the boundary), then c is small,
            -- and w is very negative, likely w < z.
            -- If |g(z)| is large (z far from boundary), c is larger, w might not be << z.

            -- But our goal is just to derive a contradiction from g(z) < 0.
            -- The key insight is that w ≥ z AND g(z) < 0 leads to contradiction.

            -- From w ≥ z and g strictly increasing: g(w) ≥ g(z) with equality iff w = z.
            -- From our bounds: g(w) > g(z)/8.
            -- Case w = z: g(z) > g(z)/8, so 7g(z) > 0. But g(z) < 0 ⇒ 7g(z) < 0. ⊥
            -- Case w > z: g(w) > g(z) and g(w) > g(z)/8.
            --   Since g(z) < 0, g(z)/8 > g(z), so g(w) > g(z)/8 is weaker than g(w) > g(z).
            --   We have g(w) > g(z) already from w > z.
            --   We also have g(w) < -g(z)/2 (from upper bound).
            --   Since g(z) < 0, -g(z)/2 > 0.
            --   So g(z) < g(w) < -g(z)/2.
            --   This gives g(z) < -g(z)/2, i.e., 3g(z) < 0. Consistent with g(z) < 0.

            -- No contradiction in Case w > z? Let me reconsider.

            -- Actually, in Case w > z, we have z < w < 0 (both negative).
            -- Apply the same argument to w: if g(w) < 0, we get a sequence...
            -- But g(w) could be positive (since g(w) < -g(z)/2 > 0 and g(w) > g(z)/8 < 0).

            -- If g(w) ≥ 0, then we have z < w with g(z) < 0 ≤ g(w).
            -- By IVT, there exists z < c < w with g(c) = 0.
            -- But we're assuming g has no zeros (from f_ne_zero etc.)? No wait, g is an
            -- auxiliary function, not f.

            -- Hmm, g could have zeros. Let's check: g(x) = f(x)*f'(x) - (1/2)*(f''(x))².
            -- g(x) = 0 means f(x)*f'(x) = (1/2)*(f''(x))².
            -- This is possible.

            -- OK so we can't use "g has no zeros."

            -- Let me try yet another approach.
            -- We're trying to prove: for all z, g(z) ≥ 0.
            -- Assume for contradiction: there exists z₀ with g(z₀) < 0.

            -- Since g is continuous and strictly increasing:
            -- - For x < z₀: g(x) < g(z₀) < 0.
            -- - For x > z₀: g(x) > g(z₀).

            -- We showed: for any ε > 0, there exists w < 0 with g(w) ∈ (-ε/4, ε).
            -- In particular, g(w) can be made arbitrarily close to 0.

            -- If z₀ < 0: we can choose w < z₀ with g(w) close to 0.
            --   But g(w) < g(z₀) < 0 since w < z₀ and g is increasing.
            --   So g(w) < 0. But we said g(w) is close to 0. Contradiction?
            --   Not quite: g(w) close to 0 from below is consistent with g(w) < 0.

            --   We have g(w) > -ε/4. If g(w) < g(z₀) < 0, then -ε/4 < g(w) < g(z₀) < 0.
            --   So g(z₀) > g(w) > -ε/4. Taking ε → 0: g(z₀) ≥ 0.
            --   But g(z₀) < 0. Contradiction!

            -- If z₀ ≥ 0: we have w < 0 ≤ z₀, so w < z₀.
            --   Same argument: g(w) < g(z₀) < 0 since w < z₀.
            --   And g(w) > -ε/4. So -ε/4 < g(w) < g(z₀).
            --   Taking ε → 0: 0 ≤ g(z₀). Contradiction with g(z₀) < 0!

            -- Great, so the argument works! The key is:
            -- For any ε > 0, there exists w with g(w) > -ε/4.
            -- And we can choose w < z₀ (by taking ε small enough that w is very negative).
            -- Then g(z₀) > g(w) > -ε/4.
            -- Taking ε → 0: g(z₀) ≥ 0.

            -- Let me formalize this.
            -- We need to show that we can choose w < z (not w ≥ z).

            -- From our construction: w = min(w₀, w₁) with w₀, w₁ depending on c = |g(z)|/2.
            -- As |g(z)| → 0 (z approaching the "boundary"), c → 0, w → -∞.
            -- But |g(z)| is fixed (it's a specific value), so c is fixed.

            -- The issue: for a given z with g(z) < 0, c = |g(z)|/2 is fixed.
            -- Our w = min(w₀, w₁) might be > z or ≤ z depending on c.

            -- Solution: choose a smaller ε.
            -- For ε > 0 (to be chosen), let wε be such that g(wε) > -ε/4.
            -- We can construct wε as before, with wε → -∞ as ε → 0.
            -- Choose ε small enough that wε < z.
            -- Then g(z) > g(wε) > -ε/4.
            -- So g(z) > -ε/4 for arbitrarily small ε.
            -- Hence g(z) ≥ 0.

            -- But wait - we need to verify that as ε → 0, wε → -∞.
            -- From the construction of hf'_approaches_zero:
            --   For any ε' > 0, there exists w' < 0 with f'(w') < ε'.
            -- As ε' → 0, w' → -∞ (since f' is positive and decreasing towards 0 at -∞).
            -- Similarly for f''.
            -- So yes, wε → -∞ as ε → 0.

            -- In our specific case, ε corresponds to c = |g(z)|/2.
            -- But we can use any ε > 0, not just c.

            -- So: choose ε = |g(z)|/4 (for example).
            -- Then there exists w with g(w) > -ε/4 = -|g(z)|/16.
            -- Since ε is smaller, w is more negative, so w < z (for z not too negative).

            -- Actually, the issue is we don't know w < z just because ε is small.
            -- We need to explicitly construct w < z.

            -- Alternative: for any x₀, there exists ε₀ such that for ε < ε₀, wε < x₀.
            -- This follows from wε → -∞ as ε → 0.
            -- Take x₀ = z. Then for small enough ε, wε < z.
            -- And g(z) > g(wε) > -ε/4.
            -- Since ε > 0 was arbitrary (just small enough), g(z) ≥ 0.

            -- Let me implement this.
            -- First, show that we can find w < z with g(w) > -δ for any δ > 0.

            have h_key : ∀ δ > 0, ∃ w < z, g w > -δ := by
              intro δ hδ
              -- Use the ε-based construction with ε = 4δ (so that g(w) > -ε/4 = -δ)
              have h4δ : 4 * δ > 0 := by linarith
              have hf0_pos_key : f 0 > 0 := hf_pos 0
              have h2f0_pos_key : 2 * f 0 + 1 > 0 := by linarith
              have heps_f'_δ : 4 * δ / (2 * f 0 + 1) > 0 := div_pos h4δ h2f0_pos_key
              obtain ⟨w₀', hw0'_neg, hf'w0'⟩ := hf'_approaches_zero (4 * δ / (2 * f 0 + 1)) heps_f'_δ
              have heps_f''_δ : Real.sqrt (4 * δ / 2) > 0 := Real.sqrt_pos.mpr (div_pos h4δ (by norm_num))
              obtain ⟨w₁', hw1'_neg, hf''w1'⟩ := hf''_approaches_zero (Real.sqrt (4 * δ / 2)) heps_f''_δ

              -- Take w' = min(w₀', w₁', z - 1) to ensure w' < z
              set w' := min (min w₀' w₁') (z - 1)
              use w'
              constructor
              · -- w' < z
                have : z - 1 < z := by linarith
                exact lt_of_le_of_lt (min_le_right (min w₀' w₁') (z - 1)) this
              · -- g(w') > -δ
                -- First, f'(w') < 4δ / (2*f(0)+1)
                have hf'w' : deriv f w' < 4 * δ / (2 * f 0 + 1) := by
                  have hw'_le_w0' : w' ≤ w₀' := le_trans (min_le_left _ _) (min_le_left _ _)
                  by_cases hw'_eq : w' = w₀'
                  · rw [hw'_eq]; exact hf'w0'
                  · exact lt_trans (hf'_strictMono (lt_of_le_of_ne hw'_le_w0' hw'_eq)) hf'w0'
                -- Similarly, f''(w') < sqrt(2δ)
                have hf''w' : deriv (deriv f) w' < Real.sqrt (4 * δ / 2) := by
                  have hw'_le_w1' : w' ≤ w₁' := le_trans (min_le_left _ _) (min_le_right _ _)
                  by_cases hw'_eq : w' = w₁'
                  · rw [hw'_eq]; exact hf''w1'
                  · exact lt_trans (hf''_strictMono (lt_of_le_of_ne hw'_le_w1' hw'_eq)) hf''w1'

                have hw'_neg : w' < 0 := lt_of_le_of_lt (min_le_left _ _) (lt_of_le_of_lt (min_le_left _ _) hw0'_neg)
                have hfw'_lt : f w' < f 0 := hf_strictMono hw'_neg
                have hfw'_pos : f w' > 0 := hf_pos w'
                have hf'w'_pos : deriv f w' > 0 := hf'_pos w'
                have hf''w'_pos : deriv (deriv f) w' > 0 := by rw [← hf''_eq]; exact hf''_pos w'

                -- g(w') = f(w')*f'(w') - (1/2)*(f''(w'))²
                -- Upper bound: f(w')*f'(w') < f(0)*(4δ/(2f(0)+1)) < 4δ
                have h_upper' : f w' * deriv f w' < 4 * δ := by
                  have h1 : f w' * deriv f w' < f 0 * (4 * δ / (2 * f 0 + 1)) :=
                    mul_lt_mul hfw'_lt (le_of_lt hf'w') hf'w'_pos (le_of_lt (hf_pos 0))
                  have h2 : f 0 * (4 * δ / (2 * f 0 + 1)) < 4 * δ := by
                    have h3 : f 0 / (2 * f 0 + 1) < 1 := by
                      rw [div_lt_one h2f0_pos_key]
                      linarith
                    calc f 0 * (4 * δ / (2 * f 0 + 1)) = f 0 / (2 * f 0 + 1) * (4 * δ) := by field_simp
                      _ < 1 * (4 * δ) := by exact mul_lt_mul_of_pos_right h3 h4δ
                      _ = 4 * δ := one_mul _
                  linarith

                -- Lower bound: (1/2)*(f''(w'))² < (1/2)*2δ = δ
                have h_sq' : (deriv (deriv f) w')^2 < 4 * δ / 2 := by
                  have h_sqrt_pos' : Real.sqrt (4 * δ / 2) > 0 := Real.sqrt_pos.mpr (div_pos h4δ (by norm_num))
                  have h_left_bound' : -(Real.sqrt (4 * δ / 2)) < deriv (deriv f) w' := by linarith
                  have h_sq_ineq' : (deriv (deriv f) w')^2 < (Real.sqrt (4 * δ / 2))^2 :=
                    sq_lt_sq' h_left_bound' hf''w'
                  have h_sq_eq' : (Real.sqrt (4 * δ / 2))^2 = 4 * δ / 2 :=
                    Real.sq_sqrt (le_of_lt (div_pos h4δ (by norm_num)))
                  linarith

                have h_lower' : -(1/2 * (deriv (deriv f) w')^2) > -δ := by
                  have : 1/2 * (deriv (deriv f) w')^2 < 1/2 * (4 * δ / 2) := by linarith
                  have : 1/2 * (deriv (deriv f) w')^2 < δ := by linarith
                  linarith

                -- g(w') > f(w')*f'(w') - δ > 0 - δ = -δ
                simp only [g]
                have hff'_pos : f w' * deriv f w' > 0 := mul_pos hfw'_pos hf'w'_pos
                linarith

            -- Now use h_key with δ = |g(z)|/2 (or any δ > 0)
            -- We get w < z with g(w) > -δ.
            -- Since g is strictly increasing and w < z: g(z) > g(w) > -δ.
            -- Since this works for any δ > 0: g(z) ≥ 0.
            -- But g(z) < 0. Contradiction.

            have h_contra : g z ≥ 0 := by
              by_contra h_neg'
              push_neg at h_neg'
              have hgz_neg : g z < 0 := h_neg'
              have habs' : |g z| / 2 > 0 := by
                have : |g z| > 0 := abs_pos.mpr (ne_of_lt hgz_neg)
                linarith
              obtain ⟨w_new, hw_new_lt_z, hgw_new⟩ := h_key (|g z| / 2) habs'
              have hgz_gt : g z > g w_new := hg_strictMono hw_new_lt_z
              -- g(z) > g(w_new) > -|g(z)|/2
              -- So g(z) > -|g(z)|/2
              -- Since g(z) < 0, |g(z)| = -g(z), so g(z) > g(z)/2, i.e., g(z)/2 > 0
              -- But g(z) < 0 implies g(z)/2 < 0. Contradiction!
              have h1 : g z > -|g z| / 2 := by linarith
              have h2 : |g z| = -g z := abs_of_neg hgz_neg
              have h3 : g z > g z / 2 := by linarith
              have h4 : g z / 2 > 0 := by linarith
              have h5 : g z / 2 < 0 := by linarith
              linarith
            linarith
        -- hgz_ge : g z ≥ 0 means 0 ≤ g z
        exact hgz_ge

    -- sInf(range g) ≥ 0
    have hg_inf_nonneg : sInf (range g) ≥ 0 := by
      rw [hg_inf_eq_zero]

    intro x
    exact pos_of_strictMono_bddBelow_inf_nonneg hg_strictMono hg_bddBelow hg_inf_nonneg x

  -- Similarly for h(x) = 2*f(x)*f''(x) - (f'(x))²
  have hh_pos : ∀ x, 2 * f x * deriv (deriv f) x - (deriv f x)^2 > 0 := by
    let h := fun x => 2 * f x * deriv (deriv f) x - (deriv f x)^2

    have hh_strictMono : StrictMono h := by
      apply strictMono_of_deriv_pos
      intro x
      have h_deriv : deriv h x = 2 * f x * deriv (deriv (deriv f)) x := by
        -- Use HasDerivAt to compute derivative
        have hd1 : HasDerivAt f (deriv f x) x := (hf_diff x).hasDerivAt
        have hd2 : HasDerivAt (deriv f) (deriv (deriv f) x) x := (hf'_diff x).hasDerivAt
        have hd3 : HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) x) x := (hf''_diff x).hasDerivAt
        -- deriv(f * f'') = f' * f'' + f * f'''
        have h_mul : HasDerivAt (fun y => f y * deriv (deriv f) y)
                     ((deriv f x) * (deriv (deriv f) x) + f x * (deriv (deriv (deriv f)) x)) x :=
          hd1.mul hd3
        -- deriv(2 * f * f'') = 2 * (f' * f'' + f * f''')
        have h_const_mul : HasDerivAt (fun y => 2 * f y * deriv (deriv f) y)
                           (2 * ((deriv f x) * (deriv (deriv f) x) + f x * (deriv (deriv (deriv f)) x))) x := by
          have : HasDerivAt (fun y => 2 * (f y * deriv (deriv f) y))
                 (2 * ((deriv f x) * (deriv (deriv f) x) + f x * (deriv (deriv (deriv f)) x))) x :=
            h_mul.const_mul 2
          convert this using 2; ring
        -- deriv((f')^2) = 2 * f' * f''
        have h_sq : HasDerivAt (fun y => (deriv f y)^2) (2 * (deriv f x) * (deriv (deriv f) x)) x := by
          have hp := hd2.pow 2
          simp only [pow_one, Nat.cast_ofNat, Nat.add_one_sub_one] at hp
          convert hp using 1
        -- deriv(h) = deriv(2*f*f'') - deriv((f')^2)
        have h_h : HasDerivAt h ((2 * ((deriv f x) * (deriv (deriv f) x) + f x * (deriv (deriv (deriv f)) x))) -
                                  (2 * (deriv f x) * (deriv (deriv f) x))) x :=
          h_const_mul.sub h_sq
        rw [h_h.deriv]
        ring
      rw [h_deriv]
      have h1 : f x > 0 := hf_pos x
      have h2 : deriv (deriv (deriv f)) x > 0 := by rw [← hf'''_eq]; exact hf'''_pos x
      have h3 : 2 * f x > 0 := by linarith
      exact mul_pos h3 h2

    -- We need helper lemmas similar to g
    -- First, show that for any ε > 0, we can find w with f'(w), f''(w) small
    -- This makes h(w) close to 0

    have hf'_approaches_zero_h : ∀ ε > 0, ∃ x₀ : ℝ, x₀ < 0 ∧ deriv f x₀ < ε := by
      intro ε hε
      have h_lt : sInf (range (deriv f)) < ε := by rw [hf'_inf_eq_zero]; exact hε
      rw [csInf_lt_iff hf'_bddBelow (range_nonempty _)] at h_lt
      obtain ⟨y, hy_mem, hy_lt⟩ := h_lt
      obtain ⟨x, hx_eq⟩ := hy_mem
      use min x (-1)
      constructor
      · exact lt_of_le_of_lt (min_le_right x (-1)) (by norm_num : (-1 : ℝ) < 0)
      · by_cases hx_le : x ≤ -1
        · rw [min_eq_left hx_le, hx_eq]; exact hy_lt
        · push_neg at hx_le
          rw [min_eq_right (le_of_lt hx_le)]
          exact lt_trans (hf'_strictMono hx_le) (hx_eq ▸ hy_lt)

    have hf''_approaches_zero_h : ∀ ε > 0, ∃ x₁ : ℝ, x₁ < 0 ∧ deriv (deriv f) x₁ < ε := by
      intro ε hε
      have h_lt : sInf (range (deriv (deriv f))) < ε := by rw [hf''_inf_eq_zero]; exact hε
      rw [csInf_lt_iff hf''_bddBelow (range_nonempty _)] at h_lt
      obtain ⟨y, hy_mem, hy_lt⟩ := h_lt
      obtain ⟨x, hx_eq⟩ := hy_mem
      use min x (-1)
      constructor
      · exact lt_of_le_of_lt (min_le_right x (-1)) (by norm_num : (-1 : ℝ) < 0)
      · by_cases hx_le : x ≤ -1
        · rw [min_eq_left hx_le, hx_eq]; exact hy_lt
        · push_neg at hx_le
          rw [min_eq_right (le_of_lt hx_le)]
          exact lt_trans (hf''_strictMono hx_le) (hx_eq ▸ hy_lt)

    -- For any δ > 0, we can find w < z with h(w) > -δ
    have h_key : ∀ z : ℝ, ∀ δ > 0, ∃ w < z, h w > -δ := by
      intro z δ hδ
      -- Choose f'(w) and f''(w) small enough
      -- h(w) = 2*f(w)*f''(w) - (f'(w))²
      -- ≥ 2*f(w)*f''(w) - (f'(w))²
      -- For w < 0: f(w) < f(0), and we want to bound h(w) from below
      -- h(w) = 2*f*f'' - (f')²
      -- ≥ -(f')² > -(f'(w))² > -ε² for f'(w) < ε
      -- So choosing ε = sqrt(δ) gives h(w) > -δ

      have hsqrt : Real.sqrt δ > 0 := Real.sqrt_pos.mpr hδ
      obtain ⟨w₀, hw0_neg, hf'w0⟩ := hf'_approaches_zero_h (Real.sqrt δ) hsqrt

      -- Take w = min(w₀, z - 1) to ensure w < z
      set w := min w₀ (z - 1)
      use w
      constructor
      · -- w < z
        have : z - 1 < z := by linarith
        exact lt_of_le_of_lt (min_le_right w₀ (z - 1)) this
      · -- h(w) > -δ
        have hf'w : deriv f w < Real.sqrt δ := by
          have hw_le : w ≤ w₀ := min_le_left w₀ (z - 1)
          by_cases hw_eq : w = w₀
          · rw [hw_eq]; exact hf'w0
          · exact lt_trans (hf'_strictMono (lt_of_le_of_ne hw_le hw_eq)) hf'w0

        have hw_neg : w < 0 := lt_of_le_of_lt (min_le_left _ _) hw0_neg
        have hfw_pos : f w > 0 := hf_pos w
        have hf'w_pos : deriv f w > 0 := hf'_pos w
        have hf''w_pos : deriv (deriv f) w > 0 := by rw [← hf''_eq]; exact hf''_pos w

        -- h(w) = 2*f(w)*f''(w) - (f'(w))²
        -- ≥ 0 - (f'(w))² (since 2*f*f'' > 0)
        -- > -(sqrt δ)² = -δ
        have h_term1_pos : 2 * f w * deriv (deriv f) w > 0 := by
          have h1 : 2 * f w > 0 := by linarith
          exact mul_pos h1 hf''w_pos

        have h_term2 : (deriv f w)^2 < δ := by
          have h_sqrt_δ_pos : Real.sqrt δ > 0 := Real.sqrt_pos.mpr hδ
          have h_left_bound_δ : -(Real.sqrt δ) < deriv f w := by linarith
          have h_sq_ineq_δ : (deriv f w)^2 < (Real.sqrt δ)^2 := sq_lt_sq' h_left_bound_δ hf'w
          have h_sq_eq_δ : (Real.sqrt δ)^2 = δ := Real.sq_sqrt (le_of_lt hδ)
          linarith

        simp only [h]
        linarith

    have hh_bddBelow : BddBelow (range h) := by
      -- h(w) = 2*f*f'' - (f')² > -(f')² > -(f'(0))² for w > 0 (since f' is increasing)
      -- For w ≤ 0: f'(w) ≤ f'(0), so (f'(w))² ≤ (f'(0))², so h(w) ≥ -(f'(0))²
      use -(deriv f 0)^2 - 1
      intro y hy
      obtain ⟨z, hz⟩ := hy
      rw [← hz]
      have hf'z_pos : deriv f z > 0 := hf'_pos z
      have hf''z_pos : deriv (deriv f) z > 0 := by rw [← hf''_eq]; exact hf''_pos z
      have hfz_pos : f z > 0 := hf_pos z
      have h_term1 : 2 * f z * deriv (deriv f) z > 0 := mul_pos (by linarith) hf''z_pos

      by_cases hz0 : z ≤ 0
      · -- For z ≤ 0: f'(z) ≤ f'(0)
        by_cases hz_eq : z = 0
        · subst hz_eq; simp only [h]; linarith
        · have hz_lt : z < 0 := lt_of_le_of_ne hz0 hz_eq
          have hf'z_lt : deriv f z < deriv f 0 := hf'_strictMono hz_lt
          have h_sq_lt : (deriv f z)^2 < (deriv f 0)^2 := by
            apply sq_lt_sq' <;> linarith
          simp only [h]
          linarith
      · -- For z > 0: h(z) > h(0) > lower bound
        push_neg at hz0
        have hhz_gt : h z > h 0 := hh_strictMono (by linarith : 0 < z)
        have hh0_lower : h 0 > -(deriv f 0)^2 - 1 := by
          simp only [h]
          have hf0_pos_h : f 0 > 0 := hf_pos 0
          have h1 : 2 * f 0 * deriv (deriv f) 0 > 0 := mul_pos (by linarith : 2 * f 0 > 0) (by rw [← hf''_eq]; exact hf''_pos 0)
          linarith
        linarith

    have hh_inf_nonneg : sInf (range h) ≥ 0 := by
      -- Similar to g: show sInf = 0 using le_antisymm
      have hh_inf_eq_zero : sInf (range h) = 0 := by
        apply le_antisymm
        · -- sInf ≤ 0: for any c > 0, find w with h(w) < c
          by_contra h_pos; push_neg at h_pos
          set c := sInf (range h)
          have hc_pos : c > 0 := h_pos
          have hh_ge_c : ∀ x, h x ≥ c := fun x => csInf_le hh_bddBelow (mem_range_self x)

          -- Find w with f'(w) and f''(w) small enough that h(w) < c
          have hf0_pos : f 0 > 0 := hf_pos 0
          have hdenom_pos : f 0 + 1 > 0 := by linarith
          have heps_f' : Real.sqrt (c / 4) > 0 := Real.sqrt_pos.mpr (div_pos hc_pos (by norm_num))
          have heps_f'' : c / (4 * f 0 + 4) > 0 := div_pos hc_pos (by linarith)

          obtain ⟨w₀, hw0_neg, hf'w0⟩ := hf'_approaches_zero_h (Real.sqrt (c / 4)) heps_f'
          obtain ⟨w₁, hw1_neg, hf''w1⟩ := hf''_approaches_zero_h (c / (4 * f 0 + 4)) heps_f''

          set z := min w₀ w₁
          have hz_neg : z < 0 := lt_of_le_of_lt (min_le_left w₀ w₁) hw0_neg

          have hf'z : deriv f z < Real.sqrt (c / 4) := by
            have hz_le : z ≤ w₀ := min_le_left w₀ w₁
            by_cases hz_eq : z = w₀
            · rw [hz_eq]; exact hf'w0
            · exact lt_trans (hf'_strictMono (lt_of_le_of_ne hz_le hz_eq)) hf'w0

          have hf''z : deriv (deriv f) z < c / (4 * f 0 + 4) := by
            have hz_le : z ≤ w₁ := min_le_right w₀ w₁
            by_cases hz_eq : z = w₁
            · rw [hz_eq]; exact hf''w1
            · exact lt_trans (hf''_strictMono (lt_of_le_of_ne hz_le hz_eq)) hf''w1

          have hfz_lt : f z < f 0 := hf_strictMono hz_neg
          have hfz_pos : f z > 0 := hf_pos z
          have hf'z_pos : deriv f z > 0 := hf'_pos z
          have hf''z_pos : deriv (deriv f) z > 0 := by rw [← hf''_eq]; exact hf''_pos z

          -- h(z) = 2*f(z)*f''(z) - (f'(z))²
          -- < 2*f(0)*(c/(4f(0)+4)) - 0
          -- = 2*f(0)*c / (4*f(0)+4)
          -- = c*f(0) / (2*f(0)+2)
          -- < c

          have h_upper : 2 * f z * deriv (deriv f) z < c / 2 := by
            have h1 : 2 * f z * deriv (deriv f) z < 2 * f 0 * (c / (4 * f 0 + 4)) := by
              have hf2 : 2 * f z < 2 * f 0 := by linarith
              apply mul_lt_mul hf2 (le_of_lt hf''z) hf''z_pos (by linarith)
            have h2 : 2 * f 0 * (c / (4 * f 0 + 4)) = c * f 0 / (2 * f 0 + 2) := by field_simp; ring
            have h3 : c * f 0 / (2 * f 0 + 2) < c / 2 := by
              have hne : 2 * f 0 + 2 ≠ 0 := by linarith
              have h4 : f 0 / (2 * f 0 + 2) < 1 / 2 := by
                rw [div_lt_div_iff₀ (by linarith : 2 * f 0 + 2 > 0) (by norm_num : (2 : ℝ) > 0)]
                linarith
              calc c * f 0 / (2 * f 0 + 2) = c * (f 0 / (2 * f 0 + 2)) := by field_simp
                _ < c * (1 / 2) := by exact mul_lt_mul_of_pos_left h4 hc_pos
                _ = c / 2 := by ring
            linarith

          have h_sq : (deriv f z)^2 < c / 4 := by
            have h_sqrt_c_pos : Real.sqrt (c / 4) > 0 := Real.sqrt_pos.mpr (div_pos hc_pos (by norm_num))
            have h_left_c : -(Real.sqrt (c / 4)) < deriv f z := by linarith
            have h_sq_c_ineq : (deriv f z)^2 < (Real.sqrt (c / 4))^2 := sq_lt_sq' h_left_c hf'z
            have h_sq_c_eq : (Real.sqrt (c / 4))^2 = c / 4 := Real.sq_sqrt (le_of_lt (div_pos hc_pos (by norm_num)))
            linarith

          have hhz_lt_c : h z < c := by
            simp only [h]
            -- h z = 2 * f z * deriv (deriv f) z - deriv f z ^ 2
            -- < 2 * f z * deriv (deriv f) z (subtracting positive)
            -- < c / 2 (from h_upper)
            -- < c
            have h_sq_pos : deriv f z ^ 2 > 0 := sq_pos_of_pos hf'z_pos
            have h1 : 2 * f z * deriv (deriv f) z - deriv f z ^ 2 < 2 * f z * deriv (deriv f) z := by linarith
            linarith

          have hhz_ge_c : h z ≥ c := hh_ge_c z
          linarith

        · -- sInf ≥ 0
          apply le_csInf (range_nonempty h)
          intro y hy
          obtain ⟨z, hz⟩ := hy
          rw [← hz]
          -- Need h(z) ≥ 0
          -- Use h_key: for any δ > 0, there exists w < z with h(w) > -δ
          -- Since h is strictly increasing, h(z) > h(w) > -δ
          -- Taking δ → 0: h(z) ≥ 0
          by_contra h_neg
          push_neg at h_neg
          have hhz_neg : h z < 0 := h_neg
          have habs : |h z| / 2 > 0 := by
            have : |h z| > 0 := abs_pos.mpr (ne_of_lt hhz_neg)
            linarith
          obtain ⟨w, hw_lt_z, hhw⟩ := h_key z (|h z| / 2) habs
          have hhz_gt : h z > h w := hh_strictMono hw_lt_z
          -- h(z) > h(w) > -|h(z)|/2
          have h1 : h z > -|h z| / 2 := by linarith
          have h2 : |h z| = -h z := abs_of_neg hhz_neg
          have h3 : h z > h z / 2 := by linarith
          have h4 : h z / 2 > 0 := by linarith
          have h5 : h z / 2 < 0 := by linarith
          linarith
      rw [hh_inf_eq_zero]

    intro x
    exact pos_of_strictMono_bddBelow_inf_nonneg hh_strictMono hh_bddBelow hh_inf_nonneg x

  -- Step 6: Derive the main result using algebraic manipulation
  intro x

  have hfx_pos : f x > 0 := hf_pos x
  have hf'x_pos : deriv f x > 0 := hf'_pos x
  have hf''x_pos : deriv (deriv f) x > 0 := by rw [← hf''_eq]; exact hf''_pos x

  -- From hg_pos: (f'')² < 2*f*f'
  have h1 : (deriv (deriv f) x)^2 < 2 * f x * deriv f x := by
    have := hg_pos x
    linarith

  -- From hh_pos: (f')² < 2*f*f''
  have h2 : (deriv f x)^2 < 2 * f x * deriv (deriv f) x := by
    have := hh_pos x
    linarith

  -- From h2: f'' > (f')²/(2f)
  have h3 : deriv (deriv f) x > (deriv f x)^2 / (2 * f x) := by
    have h2f_pos : 2 * f x > 0 := by linarith
    have h2f_ne : 2 * f x ≠ 0 := ne_of_gt h2f_pos
    rw [gt_iff_lt, div_lt_iff₀ h2f_pos]
    calc (deriv f x)^2 < 2 * f x * deriv (deriv f) x := h2
      _ = deriv (deriv f) x * (2 * f x) := by ring

  -- Square h3: (f'')² > (f')⁴/(4f²)
  have h4 : (deriv (deriv f) x)^2 > ((deriv f x)^2 / (2 * f x))^2 := by
    have hpos1 : (deriv f x)^2 / (2 * f x) > 0 := by
      apply div_pos (sq_pos_of_pos hf'x_pos)
      linarith
    exact sq_lt_sq' (by linarith) h3

  -- Combining: (f')⁴/(4f²) < (f'')² < 2*f*f'
  have h5 : ((deriv f x)^2 / (2 * f x))^2 < 2 * f x * deriv f x := by
    calc ((deriv f x)^2 / (2 * f x))^2 < (deriv (deriv f) x)^2 := h4
      _ < 2 * f x * deriv f x := h1

  -- Simplify: (f')⁴/(4f²) < 2*f*f'
  have h6 : (deriv f x)^4 / (4 * (f x)^2) < 2 * f x * deriv f x := by
    convert h5 using 1
    field_simp; ring

  -- Multiply: (f')⁴ < 8*f³*f'
  have h7 : (deriv f x)^4 < 8 * (f x)^3 * deriv f x := by
    have h_denom_pos : 4 * (f x)^2 > 0 := by positivity
    calc (deriv f x)^4
        = (deriv f x)^4 / (4 * (f x)^2) * (4 * (f x)^2) := by field_simp
      _ < 2 * f x * deriv f x * (4 * (f x)^2) := by
          exact mul_lt_mul_of_pos_right h6 h_denom_pos
      _ = 8 * (f x)^3 * deriv f x := by ring

  -- Divide by f': (f')³ < 8*f³
  have h8 : (deriv f x)^3 < 8 * (f x)^3 := by
    have : (deriv f x)^4 = (deriv f x)^3 * deriv f x := by ring
    rw [this] at h7
    exact lt_of_mul_lt_mul_of_nonneg_right h7 hf'x_pos.le

  -- Take cube root: f' < 2*f
  have h_2f_cubed : (2 * f x)^3 = 8 * (f x)^3 := by ring
  rw [← h_2f_cubed] at h8
  have h_odd_3 : Odd 3 := ⟨1, rfl⟩
  exact (h_odd_3.strictMono_pow (R := ℝ)).lt_iff_lt.mp h8
