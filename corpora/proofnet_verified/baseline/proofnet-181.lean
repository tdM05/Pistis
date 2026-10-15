import Mathlib

open Complex Filter Function Metric Finset MeasureTheory Real Set
open scoped BigOperators Topology FourierTransform RealInnerProductSpace Complex

noncomputable section

/-!

This file formalizes the classical improper-integral identity

`∫_{-∞}^{∞} cos x / (x^2 + a^2) dx = π * exp(-a) / a`  for `a > 0`,

and then uses it to compute the limit of symmetric interval integrals.

⚠️  As requested, the proof is heavily documented with step-by-step comments.

High-level plan
1. Convert the limit over `∫_{-y..y}` into an integral over `ℝ` using
   `MeasureTheory.intervalIntegral_tendsto_integral`.
2. Evaluate the whole-line integral via Fourier inversion.
   - Consider `f(x) = exp(-2π a |x|)`.
   - Compute its Fourier transform explicitly: `𝓕 f(w) = a/(π*(a^2+w^2))`.
   - Apply Fourier inversion at `t = 1/(2π)` so the kernel becomes `exp(v*I)`.
   - Take real parts to extract an integral involving `cos`.

No new axioms are introduced.
-/

/-!
## Helper lemma: a small complex-algebra identity

This identity appears when simplifying the sum of two half-line integrals.
-/

lemma inv_add_inv_conj (a w : ℝ) :
    ((↑a - ↑w * Complex.I)⁻¹ + (↑a + ↑w * Complex.I)⁻¹ : ℂ) = (2 * a / (a ^ 2 + w ^ 2) : ℂ) := by
  /-
  Step 1: Precompute the two `normSq` values we will need.
  
  The general lemma `Complex.normSq_add_mul_I` tells us:
  `normSq (a + w * I) = a^2 + w^2`.
  We will use it twice (with `w` and `-w`).
  -/
  have hnorm1 : Complex.normSq (↑a + Complex.I * ↑w) = a ^ 2 + w ^ 2 := by
    -- Step 1.1: match the lemma's shape (it is written with `+ w * I`).
    simpa [mul_comm] using (Complex.normSq_add_mul_I a w)
  have hnorm2 : Complex.normSq (↑a + -(Complex.I * ↑w)) = a ^ 2 + w ^ 2 := by
    -- Step 1.2: rewrite `↑a + -(I*↑w)` as `a + (-w) * I`.
    have : (↑a + -(Complex.I * ↑w) : ℂ) = (a : ℂ) + (-w : ℂ) * Complex.I := by
      simp [mul_comm]
    -- Step 1.3: apply the lemma with `-w`.
    simpa [this] using (Complex.normSq_add_mul_I a (-w))

  /-
  Step 2: Prove equality of complex numbers by proving equality of real and imaginary parts.
  -/
  apply Complex.ext
  · /-
    Step 2.1 (real parts):
    After expanding inverses, the real part becomes a sum of two identical fractions.
    -/
    have hMain :
        a / (a ^ 2 + w ^ 2) + a / (a ^ 2 + w ^ 2) = (↑a * 2 / (↑a ^ 2 + ↑w ^ 2) : ℂ).re := by
      -- Step 2.1.1: rewrite the denominator `↑a^2 + ↑w^2` as a real cast.
      have hden : (↑a ^ 2 + ↑w ^ 2 : ℂ) = ((a ^ 2 + w ^ 2 : ℝ) : ℂ) := by
        simp
      -- Step 2.1.2: use the library lemma describing the real part of a division by a real.
      rw [hden]
      rw [Complex.div_ofReal_re (z := (↑a * 2 : ℂ)) (x := (a ^ 2 + w ^ 2))]
      -- Step 2.1.3: simplify and close by ring-normalization.
      simp
      ring
    -- Step 2.1.4: finish the real-part goal with the `normSq` identities.
    simpa [hnorm1, hnorm2, sub_eq_add_neg, mul_comm] using hMain
  · /-
    Step 2.2 (imaginary parts):
    The imaginary parts cancel (`w/(...) + (-w)/(...) = 0`).
    -/
    have hMain :
        w / (a ^ 2 + w ^ 2) + -w / (a ^ 2 + w ^ 2) = (↑a * 2 / (↑a ^ 2 + ↑w ^ 2) : ℂ).im := by
      -- Step 2.2.1: rewrite the denominator as a real cast.
      have hden : (↑a ^ 2 + ↑w ^ 2 : ℂ) = ((a ^ 2 + w ^ 2 : ℝ) : ℂ) := by
        simp
      -- Step 2.2.2: use the library lemma for the imaginary part of a division by a real.
      rw [hden]
      rw [Complex.div_ofReal_im (z := (↑a * 2 : ℂ)) (x := (a ^ 2 + w ^ 2))]
      -- Step 2.2.3: the numerator is real, so its imaginary part is `0`.
      simp
      ring
    -- Step 2.2.4: finish with the `normSq` identities.
    simpa [hnorm1, hnorm2, sub_eq_add_neg, mul_comm] using hMain

/-!
`simp` often rewrites products as `I * ↑w` rather than `↑w * I`.
This tiny lemma is just a convenience wrapper around `inv_add_inv_conj`.
-/

lemma inv_add_inv_conj_I_mul (a w : ℝ) :
    ((↑a - Complex.I * ↑w)⁻¹ + (↑a + Complex.I * ↑w)⁻¹ : ℂ) = (2 * a / (a ^ 2 + w ^ 2) : ℂ) := by
  -- Step 1: commute `I` and `↑w` so the expression matches `inv_add_inv_conj`.
  simpa [mul_comm, mul_left_comm, mul_assoc] using (inv_add_inv_conj a w)

/-!
## Integrability lemmas

We will need integrability of the rational function `(x^2 + a^2)⁻¹` (for `a>0`),
and then integrability of `cos x / (x^2 + a^2)` via domination.
-/

lemma integrable_inv_sq_add_sq (a : ℝ) (ha : 0 < a) : Integrable (fun x : ℝ => (x ^ 2 + a ^ 2)⁻¹) := by
  /-
  Step 1: record `a ≠ 0` (needed for `field_simp`).
  -/
  have ha0 : a ≠ 0 := ne_of_gt ha

  /-
  Step 2: start from the known integrability lemma
  `integrable_inv_one_add_sq : Integrable (fun y : ℝ => (1 + y^2)⁻¹)`.
  -/
  have hbase : Integrable (fun y : ℝ => (1 + y ^ 2)⁻¹) := by
    simpa using (integrable_inv_one_add_sq : Integrable (fun y : ℝ => (1 + y ^ 2)⁻¹))

  /-
  Step 3: use a scaling change-of-variables lemma:
  `integrable_comp_mul_left_iff` says integrability is preserved by the map `x ↦ R*x` (for `R ≠ 0`).
  We will use the scaling factor `R = 1/a`.
  -/
  have hR : (1 / a) ≠ 0 := by
    simp [ha0]
  have hcomp : Integrable (fun x : ℝ => (1 + (((1 / a) * x) ^ 2))⁻¹) := by
    -- Step 3.1: apply the change-of-variables lemma to `hbase`.
    exact (MeasureTheory.integrable_comp_mul_left_iff
      (g := fun y : ℝ => (1 + y ^ 2)⁻¹) (R := (1 / a)) hR).2 hbase

  /-
  Step 4: rewrite the target function into a scaled version of the base integrable function.

  Algebraically:
  `(x^2 + a^2)⁻¹ = (a^2)⁻¹ * (1 + ((x/a)^2))⁻¹`.
  -/
  have hEq : (fun x : ℝ => (x ^ 2 + a ^ 2)⁻¹)
      = fun x : ℝ => (a ^ 2)⁻¹ * (1 + ((1 / a) * x) ^ 2)⁻¹ := by
    funext x
    -- Step 4.1: clear denominators (using `a ≠ 0`).
    field_simp [ha0]
    -- Step 4.2: finish by ring arithmetic.
    ring

  /-
  Step 5: conclude integrability by pulling out the constant factor `(a^2)⁻¹`.
  -/
  have htarget : Integrable (fun x : ℝ => (a ^ 2)⁻¹ * (1 + ((1 / a) * x) ^ 2)⁻¹) :=
    hcomp.const_mul (c := (a ^ 2)⁻¹)
  simpa [hEq] using htarget

lemma integrable_cos_div_sq_add_sq (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.cos x / (x ^ 2 + a ^ 2)) := by
  /-
  Step 1: start from the already-proved integrability of `(x^2 + a^2)⁻¹`.
  -/
  have hInv : Integrable (fun x : ℝ => (x ^ 2 + a ^ 2)⁻¹) :=
    integrable_inv_sq_add_sq a ha

  /-
  Step 2: show the target function is a.e. strongly measurable.
  This is easy because it is continuous (the denominator never vanishes when `a>0`).
  -/
  have hMeas : AEStronglyMeasurable (fun x : ℝ => Real.cos x / (x ^ 2 + a ^ 2)) := by
    /-
    Step 2.1: Prove continuity of the numerator and denominator.
    -/
    have hcont_num : Continuous (fun x : ℝ => Real.cos x) := by
      fun_prop
    have hcont_den : Continuous (fun x : ℝ => x ^ 2 + a ^ 2) := by
      fun_prop
    /-
    Step 2.2: The denominator never vanishes because `x^2 + a^2 > 0` when `a>0`.
    -/
    have hden_ne : ∀ x : ℝ, x ^ 2 + a ^ 2 ≠ 0 := by
      intro x
      have : 0 < x ^ 2 + a ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_pos ha)
      exact ne_of_gt this
    /-
    Step 2.3: Conclude continuity (hence a.e. strong measurability) of the quotient.
    -/
    have hcont : Continuous (fun x : ℝ => Real.cos x / (x ^ 2 + a ^ 2)) :=
      hcont_num.div hcont_den hden_ne
    exact hcont.aestronglyMeasurable

  /-
  Step 3: show a pointwise domination on norms:
  `|cos x / (x^2+a^2)| ≤ (x^2+a^2)⁻¹` using `|cos x| ≤ 1`.
  -/
  have hBound : ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
      ‖Real.cos x / (x ^ 2 + a ^ 2)‖ ≤ (x ^ 2 + a ^ 2)⁻¹ := by
    refine MeasureTheory.ae_of_all _ (fun x => ?_)
    -- Step 3.1: in `ℝ`, the norm is the absolute value.
    -- (Note: `simp` also expands `abs_div` for us.)
    simp [Real.norm_eq_abs]
    -- Step 3.2: the denominator is strictly positive since `a^2 > 0`.
    have hden_pos : 0 < x ^ 2 + a ^ 2 := by
      -- `x^2 ≥ 0` and `a^2 > 0`.
      exact add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_pos ha)
    -- Step 3.3: simplify `|x^2 + a^2|` using positivity.
    calc
      |Real.cos x| / |x ^ 2 + a ^ 2| = |Real.cos x| / (x ^ 2 + a ^ 2) := by
        simp [abs_of_pos hden_pos]
      _ ≤ (1 : ℝ) / (x ^ 2 + a ^ 2) := by
        -- Step 3.4: divide the inequality `|cos x| ≤ 1` by a nonnegative denominator.
        exact div_le_div_of_nonneg_right (abs_cos_le_one x) (le_of_lt hden_pos)
      _ = (x ^ 2 + a ^ 2)⁻¹ := by
        simp [one_div]

  /-
  Step 4: apply `Integrable.mono'` with the dominating integrable function.
  -/
  exact Integrable.mono' hInv hMeas hBound

/-!
## Fourier-analytic computation

We define `f(x) = exp(-2π a |x|)` (complex-valued) and compute its Fourier transform.
Then we apply Fourier inversion to extract the desired integral of `cos`.
-/

-- Define `f(x) = exp(-2π a |x|)` as a complex-valued function.
def f (a : ℝ) (x : ℝ) : ℂ := (Real.exp (-2 * Real.pi * a * |x|) : ℂ)

lemma fourier_f (a : ℝ) (ha : 0 < a) (w : ℝ) : 𝓕 (f a) w = (a / (Real.pi * (a ^ 2 + w ^ 2)) : ℂ) := by
  /-
  Step 1: Expand the definition of the Fourier transform on `ℝ`.
  The lemma `Real.fourierIntegral_real_eq_integral_exp_smul` gives an explicit integral kernel.
  -/
  have hdef : 𝓕 (f a) w
      = ∫ v : ℝ, cexp (↑(-2 * π * v * w) * I) * (Real.exp (-2 * π * a * |v|) : ℂ) := by
    simp [Real.fourier_real_eq_integral_exp_smul, f, smul_eq_mul]

  /-
  Step 2: Introduce the integrand as a standalone function `g`.
  This is just to avoid repeating a long expression.
  -/
  let g : ℝ → ℂ := fun v => cexp (↑(-2 * π * v * w) * I) * (Real.exp (-2 * π * a * |v|) : ℂ)

  /-
  Step 3: We split the integral into negative and positive half-lines.
  Concretely, we will compute
  `∫_{(-∞,0]} g + ∫_{(0,∞)} g`.
  -/

  -- Step 3.1: define the complex coefficients in the exponent on each half-line.
  -- On `(-∞,0]`, `|v| = -v` so the real exponent becomes `(+2πa) * v`.
  -- On `(0,∞)`, `|v| = v` so the real exponent becomes `(-2πa) * v`.
  let Aneg : ℂ := (2 * Real.pi * a : ℂ) + (-(2 * Real.pi * w) : ℂ) * I
  let Apos : ℂ := (-2 * Real.pi * a : ℂ) + (-(2 * Real.pi * w) : ℂ) * I

  -- Step 3.2: rewrite `g` as a single exponential on `(-∞,0]`.
  have hg_Iic : EqOn g (fun v : ℝ => cexp (Aneg * (v : ℂ))) (Set.Iic 0) := by
    intro v hv
    -- Step 3.2.1: extract the inequality `v ≤ 0` from membership.
    have hv0 : v ≤ 0 := by simpa using hv
    -- Step 3.2.2: use `|v| = -v`.
    have habs : |v| = -v := by simp [abs_of_nonpos hv0]
    -- Step 3.2.3: convert the real exponential to a complex exponential, then collect terms.
    simp [g, Aneg, habs, Complex.ofReal_exp, Complex.exp_add, mul_add,
      mul_left_comm, mul_comm]

  -- Step 3.3: similarly, rewrite `g` as a single exponential on `(0,∞)`.
  have hg_Ioi : EqOn g (fun v : ℝ => cexp (Apos * (v : ℂ))) (Set.Ioi 0) := by
    intro v hv
    -- Step 3.3.1: extract `0 < v`.
    have hv0 : 0 < v := by simpa using hv
    -- Step 3.3.2: use `|v| = v`.
    have habs : |v| = v := by simp [abs_of_nonneg (le_of_lt hv0)]
    -- Step 3.3.3: same algebraic collection as before.
    simp [g, Apos, habs, Complex.ofReal_exp, Complex.exp_add, mul_add,
      mul_left_comm, mul_comm]

  /-
  Step 4: Prove integrability of `g` on each half-line.
  We will use the dedicated lemmas about exponential integrals:
  - `integrableOn_exp_mul_complex_Iic` when the real part is positive.
  - `integrableOn_exp_mul_complex_Ioi` when the real part is negative.
  -/
  have hAneg_re : 0 < Aneg.re := by
    -- The real part of `Aneg` is `2πa`.
    simp [Aneg, ha, Real.pi_pos]
  have hApos_re : Apos.re < 0 := by
    -- The real part of `Apos` is `-2πa`.
    simp [Apos, ha, Real.pi_pos]

  have hInt_Iic : IntegrableOn g (Set.Iic 0) := by
    -- Step 4.1: reduce to an exponential integrable on `Iic` using `hg_Iic`.
    have : IntegrableOn (fun v : ℝ => cexp (Aneg * (v : ℂ))) (Set.Iic 0) :=
      integrableOn_exp_mul_complex_Iic (a := Aneg) hAneg_re 0
    exact this.congr_fun (hg_Iic.symm) measurableSet_Iic
  have hInt_Ioi : IntegrableOn g (Set.Ioi 0) := by
    -- Step 4.2: reduce to an exponential integrable on `Ioi` using `hg_Ioi`.
    have : IntegrableOn (fun v : ℝ => cexp (Apos * (v : ℂ))) (Set.Ioi 0) :=
      integrableOn_exp_mul_complex_Ioi (a := Apos) hApos_re 0
    exact this.congr_fun (hg_Ioi.symm) measurableSet_Ioi

  /-
  Step 5: Split the whole integral into the sum over `Iic 0` and `Ioi 0`.
  The lemma `intervalIntegral.integral_Iic_add_Ioi` does precisely this.
  -/
  have hsplit : (∫ v : ℝ, g v) = (∫ v in Set.Iic 0, g v) + (∫ v in Set.Ioi 0, g v) := by
    simpa using (intervalIntegral.integral_Iic_add_Ioi (μ := (volume : Measure ℝ))
      (f := g) (b := (0 : ℝ)) hInt_Iic hInt_Ioi).symm

  /-
  Step 6: Compute each half-line integral explicitly.
  We use the evaluation lemmas `integral_exp_mul_complex_Iic/Ioi`.
  -/
  have hIic : (∫ v in Set.Iic 0, g v) = 1 / Aneg := by
    -- Step 6.1: rewrite using `hg_Iic` so we can apply `integral_exp_mul_complex_Iic`.
    have : (∫ v : ℝ in Set.Iic (0 : ℝ), g v) = ∫ v : ℝ in Set.Iic (0 : ℝ), cexp (Aneg * (v : ℂ)) := by
      refine setIntegral_congr_fun measurableSet_Iic ?_
      intro v hv
      simpa using (hg_Iic hv)
    -- Step 6.2: the integral of `exp(Aneg * v)` over `(-∞,0]` is `exp(Aneg*0)/Aneg = 1/Aneg`.
    simpa [this, one_div] using (integral_exp_mul_complex_Iic (a := Aneg) hAneg_re 0)
  have hIoi : (∫ v in Set.Ioi 0, g v) = -1 / Apos := by
    -- Step 6.3: rewrite using `hg_Ioi` then apply `integral_exp_mul_complex_Ioi`.
    have : (∫ v : ℝ in Set.Ioi (0 : ℝ), g v) = ∫ v : ℝ in Set.Ioi (0 : ℝ), cexp (Apos * (v : ℂ)) := by
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro v hv
      simpa using (hg_Ioi hv)
    simpa [this, one_div] using (integral_exp_mul_complex_Ioi (a := Apos) hApos_re 0)

  /-
  Step 7: Combine the two half-line integrals.
  -/
  have htotal : (∫ v : ℝ, g v) = (1 / Aneg) + (-1 / Apos) := by
    -- Just substitute `hsplit`, `hIic`, and `hIoi`.
    simp [hsplit, hIic, hIoi, add_comm]

  /-
  Step 8: Simplify the algebraic expression `(1/Aneg) + (-1/Apos)`.
  We factor out `2π` and reduce to the previously proved lemma `inv_add_inv_conj`.
  -/
  have hAneg : Aneg = (2 * Real.pi : ℂ) * (↑a - ↑w * I) := by
    -- pure algebra
    unfold Aneg
    ring
  have hApos : Apos = (2 * Real.pi : ℂ) * (-(↑a + ↑w * I)) := by
    unfold Apos
    ring

  have hsum_simpl : (1 / Aneg) + (-1 / Apos) = (a / (Real.pi * (a ^ 2 + w ^ 2)) : ℂ) := by
    -- Step 8.1: substitute `Aneg` and `Apos`.
    -- Step 8.2: use `one_div` and simplify the common factor `2π`.
    -- Step 8.3: use `inv_add_inv_conj` to compute the remaining sum.
    -- Step 8.4: finish with `field_simp` to clear denominators.
    -- We follow the same overall structure as the scratch proof:
    -- 1) simplify constants so only the core rational identity remains,
    -- 2) solve that identity using `inv_add_inv_conj_I_mul`.

    -- Step 8.4.1: simplify the outer constants (`2π`) and clear them with `field_simp`.
    simp [hAneg, hApos, one_div, mul_comm, mul_left_comm]
    field_simp [Real.pi_ne_zero]

    -- Step 8.4.2: the goal is now a pure identity about the two poles.
    -- Convert the remaining divisions `1 / z` into inverses `z⁻¹`.
    simp [one_div]

    -- Step 8.4.3: simplify the second summand.
    --
    -- We show
    --   `- ( (-(I*w) + -a)⁻¹ ) = (a + I*w)⁻¹`.
    have hNegInv : (-( (-(Complex.I * (w : ℂ)) + -(a : ℂ) : ℂ)⁻¹) ) =
        ((a : ℂ) + Complex.I * (w : ℂ))⁻¹ := by
      have h : (-(Complex.I * (w : ℂ)) + -(a : ℂ) : ℂ) = -((a : ℂ) + Complex.I * (w : ℂ)) := by
        ring
      rw [h]
      rw [inv_neg]
      simp

    -- Use `hNegInv` to rewrite the left-hand side.
    -- After this rewrite, we can apply `inv_add_inv_conj_I_mul`.
    --
    -- Note: at this stage the two terms are exactly
    --   `(↑a - I*↑w)⁻¹ + (↑a + I*↑w)⁻¹`.
    --
    -- Finish:
    --
    -- 1) replace the second term using `hNegInv`,
    -- 2) apply `inv_add_inv_conj_I_mul`,
    -- 3) tidy up the right-hand side by commutativity.
    --
    -- (We keep the final arithmetic explicit to avoid brittle simp loops.)
    have hCore : ((↑a - Complex.I * ↑w)⁻¹ + ((a : ℂ) + Complex.I * (w : ℂ))⁻¹ : ℂ)
        = (2 * a / (a ^ 2 + w ^ 2) : ℂ) := by
      -- `simp` converts `(a:ℂ) + I*(w:ℂ)` into `↑a + I*↑w`.
      simpa using (inv_add_inv_conj_I_mul a w)

    -- Rewrite the goal using `hNegInv`, then close with `hCore` and a final cast simplification.
    --
    -- `ring` will close the remaining real commutativity fact after `norm_cast`.
    --
    -- Start:
    --
    -- Replace the second inverse term.
    -- (We use `rw` to keep the transformation transparent.)
    --
    -- Note that `hNegInv` is phrased with `w : ℂ`; we rewrite it at `w`.
    --
    -- After rewriting, the goal becomes exactly `hCore` (up to commutativity of `2*a`).
    --
    -- Finish by `norm_cast` + `ring`.
    --
    -- 1) rewrite using `hNegInv`,
    -- 2) rewrite using `hCore`,
    -- 3) discharge the remaining cast goal.
    --
    -- Step:
    --
    -- `simp` with `hNegInv` replaces the second summand.
    --
    -- Then:
    --
    -- `rw [hCore]` replaces the whole left side.
    --
    -- Finally:
    --
    -- `norm_cast; ring` matches `2*a/(...)` with `a*2/(...)`.
    --
    -- Implementation:
    --
    -- Rewrite LHS.
    simp [hNegInv]
    -- Now apply the core identity.
    -- (The goal is now exactly `hCore`'s left-hand side.)
    --
    -- So we rewrite using `hCore`.
    rw [hCore]
    -- Finish the remaining cast/commutativity goal.
    norm_cast
    ring

  /-
  Step 9: Rewrite back to the original goal using `hdef`.
  -/
  calc
    𝓕 (f a) w
        = ∫ v : ℝ, g v := by
            -- `hdef` expresses `𝓕 (f a) w` as the integral of `g`.
            simp [hdef, g]
    _ = (1 / Aneg) + (-1 / Apos) := htotal
    _ = (a / (Real.pi * (a ^ 2 + w ^ 2)) : ℂ) := hsum_simpl

/-!
### Integrability of `f` itself

For Fourier inversion we need `Integrable (f a)`.
We prove integrability of the underlying real function by splitting into half-lines.
-/

lemma integrable_real_exp_abs (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp (-2 * Real.pi * a * |x|)) := by
  /-
  Step 1: show integrability on `(-∞,0]` by rewriting `|x| = -x`.
  -/
  have hIic : IntegrableOn (fun x : ℝ => Real.exp (-2 * Real.pi * a * |x|)) (Set.Iic (0 : ℝ)) := by
    have hEq : EqOn (fun x : ℝ => Real.exp ((2 * Real.pi * a) * x))
        (fun x : ℝ => Real.exp (-2 * Real.pi * a * |x|)) (Set.Iic 0) := by
      intro x hx
      have hx0 : x ≤ 0 := by simpa using hx
      have habs : |x| = -x := by simp [abs_of_nonpos hx0]
      simp [habs, mul_left_comm, mul_comm]
    have hbase : IntegrableOn (fun x : ℝ => Real.exp ((2 * Real.pi * a) * x)) (Set.Iic 0) :=
      integrableOn_exp_mul_Iic (a := (2 * Real.pi * a)) (by nlinarith [Real.pi_pos, ha]) 0
    exact hbase.congr_fun hEq measurableSet_Iic

  /-
  Step 2: show integrability on `(0,∞)` by rewriting `|x| = x`.
  -/
  have hIoi : IntegrableOn (fun x : ℝ => Real.exp (-2 * Real.pi * a * |x|)) (Set.Ioi (0 : ℝ)) := by
    have hEq : EqOn (fun x : ℝ => Real.exp ((-2 * Real.pi * a) * x))
        (fun x : ℝ => Real.exp (-2 * Real.pi * a * |x|)) (Set.Ioi 0) := by
      intro x hx
      have hx0 : 0 < x := by simpa using hx
      have habs : |x| = x := by simp [abs_of_nonneg (le_of_lt hx0)]
      simp [habs, mul_left_comm, mul_comm]
    have hbase : IntegrableOn (fun x : ℝ => Real.exp ((-2 * Real.pi * a) * x)) (Set.Ioi 0) :=
      integrableOn_exp_mul_Ioi (a := (-2 * Real.pi * a)) (by nlinarith [Real.pi_pos, ha]) 0
    exact hbase.congr_fun hEq measurableSet_Ioi

  /-
  Step 3: glue the two halves using `Iic 0 ∪ Ioi 0 = univ`, then convert `IntegrableOn univ`
  to `Integrable`.
  -/
  have hUnion : IntegrableOn (fun x : ℝ => Real.exp (-2 * Real.pi * a * |x|))
      (Set.Iic (0 : ℝ) ∪ Set.Ioi (0 : ℝ)) := hIic.union hIoi
  have hUniv : IntegrableOn (fun x : ℝ => Real.exp (-2 * Real.pi * a * |x|)) (Set.univ : Set ℝ) := by
    simpa [Set.Iic_union_Ioi] using hUnion
  simpa [MeasureTheory.integrableOn_univ] using hUniv

lemma integral_cos_div_sq_add_sq (a : ℝ) (ha : 0 < a) :
    (∫ x : ℝ, Real.cos x / (x ^ 2 + a ^ 2)) = Real.pi * (Real.exp (-a) / a) := by
  /-
  Step 1: Set up the Fourier-analytic objects.
  -/
  -- The complex function whose Fourier transform we will compute.
  let F : ℝ → ℂ := f a

  -- Step 1.1: Integrability of `F` (needed for Fourier inversion).
  have hF_integrable_real : Integrable (fun x : ℝ => Real.exp (-2 * Real.pi * a * |x|)) :=
    integrable_real_exp_abs a ha
  have hF_integrable : Integrable F := by
    /-
    Step 1.1.1: Cast the integrable real function to an integrable complex function.

    IMPORTANT TECHNICAL NOTE:
    `simp` has a simp-lemma `Complex.ofReal_exp` that rewrites
    `((Real.exp r : ℝ) : ℂ)` into `Complex.exp r`.

    Therefore, if we try to do everything in a single line

      `simpa [F, f] using (Integrable.ofReal ... hF_integrable_real)`

    Lean will *simplify the term* into a `Complex.exp`-normal form, while the goal still
    has the `Real.exp`-normal form coming from the definition of `f`.

    To avoid this mismatch, we proceed in explicit substeps:
    - Step 1.1.1.1: get integrability of the coerced real exponential.
    - Step 1.1.1.2: let `simp` put it into `Complex.exp` normal form.
    - Step 1.1.1.3: rewrite `F` into the *same* normal form.
    - Step 1.1.1.4: finish by rewriting.
    -/
    -- Step 1.1.1.1: cast the real integrable function into `ℂ` (no simp yet!).
    have h1 : Integrable (fun x : ℝ => ((Real.exp (-2 * Real.pi * a * |x|)) : ℂ)) := by
      exact MeasureTheory.Integrable.ofReal (𝕜 := ℂ) hF_integrable_real

    -- Step 1.1.1.2: rewrite the coercion of `Real.exp` into `Complex.exp`.
    have h2 : Integrable (fun x : ℝ =>
        Complex.exp (-(2 * (Real.pi : ℂ) * (a : ℂ) * ((|x| : ℝ) : ℂ)))) := by
      simpa using h1

    -- Step 1.1.1.3: put `F` itself into the same `Complex.exp` normal form.
    have hEq : F = (fun x : ℝ =>
        Complex.exp (-(2 * (Real.pi : ℂ) * (a : ℂ) * ((|x| : ℝ) : ℂ)))) := by
      funext x
      simp [F, f, mul_left_comm, mul_comm]

    -- Step 1.1.1.4: rewrite by `hEq`.
    simpa [hEq] using h2

  -- Step 1.2: Compute the Fourier transform of `F`.
  have hFourier : ∀ w : ℝ, 𝓕 F w = (a / (Real.pi * (a ^ 2 + w ^ 2)) : ℂ) := by
    intro w
    simpa [F] using fourier_f a ha w

  -- Step 1.3: Prove integrability of the Fourier transform (needed for Fourier inversion).
  have hG : Integrable (fun w : ℝ => (a / (Real.pi * (a ^ 2 + w ^ 2)) : ℂ)) := by
    -- Step 1.3.1: first show integrability of `(a^2 + w^2)⁻¹`.
    have hInv : Integrable (fun w : ℝ => (a ^ 2 + w ^ 2)⁻¹) := by
      -- This is the same lemma as before, up to commutativity.
      simpa [add_comm, add_left_comm, add_assoc] using (integrable_inv_sq_add_sq a ha)
    -- Step 1.3.2: rewrite `a/(π*(a^2+w^2))` as a constant multiple of `(a^2+w^2)⁻¹`.
    have hReal : Integrable (fun w : ℝ => a / (Real.pi * (a ^ 2 + w ^ 2))) := by
      have hEq : (fun w : ℝ => a / (Real.pi * (a ^ 2 + w ^ 2)))
          = fun w : ℝ => (a / Real.pi) * (a ^ 2 + w ^ 2)⁻¹ := by
        funext w
        field_simp [Real.pi_ne_zero]
      simpa [hEq] using hInv.const_mul (c := (a / Real.pi))
    -- Step 1.3.3: cast to `ℂ`.
    -- `simp` rewrites `((r/s : ℝ) : ℂ)` as `(r : ℂ) / (s : ℂ)`.
    have hCast : Integrable (fun w : ℝ => ((a / (Real.pi * (a ^ 2 + w ^ 2)) : ℝ) : ℂ)) :=
      hReal.ofReal
    simpa [Complex.ofReal_div] using hCast

  have hFourier_integrable : Integrable (𝓕 F) := by
    -- Step 1.3.4: transfer integrability from `g` to `𝓕 F` using the explicit formula.
    have hEq : (fun w : ℝ => (a / (Real.pi * (a ^ 2 + w ^ 2)) : ℂ)) =ᵐ[volume] (𝓕 F) := by
      refine MeasureTheory.ae_of_all _ (fun w => ?_)
      -- Use the pointwise identity `hFourier`.
      simpa using (hFourier w).symm
    exact hG.congr hEq

  /-
  Step 2: Apply Fourier inversion at the special point `t = 1/(2π)`.
  At this `t`, the inverse Fourier kernel becomes `exp(v*I)`.
  -/
  let t : ℝ := (1 / (2 * Real.pi) : ℝ)
  have ht_cont : ContinuousAt F t := by
    /-
    Step 2.1: Prove continuity of `F` at `t`.

    As in Step 1.1.1, `fun_prop` prefers to work with the `Complex.exp` normal form.
    So we first rewrite `F` into this normal form, then let `fun_prop` close the goal.
    -/
    -- Step 2.1.1: rewrite `F` into the `Complex.exp` normal form.
    have hEq : F = (fun x : ℝ =>
        Complex.exp (-(2 * (Real.pi : ℂ) * (a : ℂ) * ((|x| : ℝ) : ℂ)))) := by
      funext x
      simp [F, f, mul_left_comm, mul_comm]

    -- Step 2.1.2: continuity of the right-hand side is automatic.
    -- Step 2.1.3: rewrite back using `hEq`.
    simpa [hEq] using (by
      fun_prop :
        ContinuousAt (fun x : ℝ =>
          Complex.exp (-(2 * (Real.pi : ℂ) * (a : ℂ) * ((|x| : ℝ) : ℂ)))) t)
  have hInv : 𝓕⁻ (𝓕 F) t = F t :=
    hF_integrable.fourierInv_fourier_eq hFourier_integrable ht_cont

  /-
  Step 3: Rewrite the inverse Fourier transform at `t = 1/(2π)` as an explicit integral.
  -/
  have hInv' :
      (∫ v : ℝ, Complex.exp (↑v * Complex.I) * (𝓕 F v)) = F t := by
    -- `Real.fourierIntegralInv_eq'` gives the general formula.
    -- At `t = 1/(2π)` the exponential simplifies to `exp(v*I)`.
    -- We also rewrite `•` as `*` since scalar multiplication on `ℂ` is multiplication.
    simpa [t, Real.fourierInv_eq', smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hInv

  /-
  Step 4: Substitute the explicit formula for `𝓕 F`.
  -/
  have hInv'' :
      (∫ v : ℝ, Complex.exp (↑v * Complex.I) * (a / (Real.pi * (a ^ 2 + v ^ 2)) : ℂ)) = F t := by
    -- Replace `𝓕 F v` pointwise using `hFourier`.
    refine (integral_congr_ae ?_).trans hInv'
    refine MeasureTheory.ae_of_all _ (fun v => ?_)
    simp [hFourier v]

  /-
  Step 5: Simplify the right-hand side `F t`.
  Since `t = 1/(2π) > 0`, we have `|t| = t`, hence
  `F t = exp(-2π a t) = exp(-a)`.
  -/
  have ht_pos : (0 : ℝ) < t := by
    -- `t = 1/(2π)` and `2π > 0`.
    have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_pos]
    exact one_div_pos.mpr h2pi_pos
  have hFt : F t = (Real.exp (-a) : ℂ) := by
    -- Step 5.1: first prove the corresponding real identity about the exponent.
    have hRealExp : Real.exp (-2 * Real.pi * a * |t|) = Real.exp (-a) := by
      have habs : |t| = t := by
        simpa using abs_of_pos ht_pos
      rw [habs]
      -- Now simplify the exponent `-2π*a*(1/(2π))`.
      have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by
        exact ne_of_gt (by nlinarith [Real.pi_pos])
      -- Reduce equality of exponentials to equality of exponents.
      congr 1
      -- Expand `t = 1/(2π)` and clear denominators.
      dsimp [t]
      field_simp [h2pi_ne]
    -- Step 5.2: cast the real identity to `ℂ`.
    -- Unfold `F` and use `hRealExp`.
    dsimp [F, f]
    -- `F t` is a coercion of the real exponential.
    simpa using congrArg (fun r : ℝ => (r : ℂ)) hRealExp

  -- Rewrite `hInv''` using `hFt`.
  have hInv_final :
      (∫ v : ℝ, Complex.exp (↑v * Complex.I) * (a / (Real.pi * (a ^ 2 + v ^ 2)) : ℂ))
        = (Real.exp (-a) : ℂ) := by
    simpa [hFt] using hInv''

  /-
  Step 6: Take real parts of the identity and use `integral_re` to move `re` inside.
  -/
  have hInt : Integrable (fun v : ℝ => Complex.exp (↑v * Complex.I)
        * (a / (Real.pi * (a ^ 2 + v ^ 2)) : ℂ)) := by
    -- Step 6.1: dominate the norm by the integrable function `v ↦ a/(π*(a^2+v^2))`.
    -- This works because `‖exp(↑v*I)‖ = 1`.
    refine Integrable.mono hG (by fun_prop) ?_
    refine MeasureTheory.ae_of_all _ (fun v => ?_)
    simp [Complex.norm_exp]

  -- Step 6.1: take real parts and use `integral_re`.
  have hReEq :
      (∫ v : ℝ, (Complex.exp (↑v * Complex.I) * (a / (Real.pi * (a ^ 2 + v ^ 2)) : ℂ)).re)
        = Real.exp (-a) := by
    /-
    Step 6.2: Take real parts of `hInv_final`.
    This gives an equality of real numbers:
    `re(∫ integrand) = re(exp(-a))`.
    -/
    have hRe :
        (∫ v : ℝ, Complex.exp (↑v * Complex.I) * (a / (Real.pi * (a ^ 2 + v ^ 2)) : ℂ)).re
          = (Real.exp (-a) : ℂ).re := by
      simpa using congrArg Complex.re hInv_final

    /-
    Step 6.3: Move the real-part map inside the integral.
    The lemma `integral_re hInt` says:
    `∫ re(integrand v) = re(∫ integrand v)`.
    -/
    have hRe' :
        (∫ v : ℝ, (Complex.exp (↑v * Complex.I) * (a / (Real.pi * (a ^ 2 + v ^ 2)) : ℂ)).re)
          = (Real.exp (-a) : ℂ).re := by
      calc
        (∫ v : ℝ, (Complex.exp (↑v * Complex.I) * (a / (Real.pi * (a ^ 2 + v ^ 2)) : ℂ)).re)
            = (∫ v : ℝ, Complex.exp (↑v * Complex.I) * (a / (Real.pi * (a ^ 2 + v ^ 2)) : ℂ)).re := by
                -- This is exactly `integral_re hInt`.
                simpa using (integral_re hInt)
        _ = (Real.exp (-a) : ℂ).re := hRe

    /-
    Step 6.4: Simplify `re((Real.exp (-a) : ℂ)) = Real.exp (-a)`.

    IMPORTANT TECHNICAL NOTE:
    We deliberately avoid `simp` here because it tends to rewrite
    `((Real.exp (-a) : ℝ) : ℂ)` into `Complex.exp (-a)`, after which the real-part
    simplification becomes harder.

    Instead we use the direct lemma `Complex.ofReal_re`.
    -/
    have hRhs : (Real.exp (-a) : ℂ).re = Real.exp (-a) := by
      -- Step 6.4.1: `re` of a real number coerced to `ℂ` is itself.
      -- (`Complex.ofReal_re` is the exact lemma we want.)
      simpa using (Complex.ofReal_re (Real.exp (-a)))

    -- Step 6.4.2: combine `hRe'` with `hRhs` without any additional simp rewriting.
    calc
      (∫ v : ℝ, (Complex.exp (↑v * Complex.I) * (a / (Real.pi * (a ^ 2 + v ^ 2)) : ℂ)).re)
          = (Real.exp (-a) : ℂ).re := hRe'
      _ = Real.exp (-a) := hRhs

  /-
  Step 7: Simplify the integrand real part into a real expression involving `cos`.
  We proved a robust simplification lemma for this pattern.
  -/
  have hReIntegrand :
      (fun v : ℝ => (Complex.exp (↑v * Complex.I) * (a / (Real.pi * (a ^ 2 + v ^ 2)) : ℂ)).re)
        = fun v : ℝ => (a / (Real.pi * (a ^ 2 + v ^ 2))) * Real.cos v := by
    funext v
    -- We use the proven computation from the scratch development (reproduced here).
    -- The proof is identical to `tmp/check_re_integrand13.lean`.
    --
    -- Step 7.1: expand `re(z*w)`.
    simp [Complex.mul_re]
    -- Step 7.2: rewrite the denominator as a real cast.
    have hden : (↑Real.pi * (↑a ^ 2 + ↑v ^ 2) : ℂ) = ((Real.pi * (a ^ 2 + v ^ 2) : ℝ) : ℂ) := by
      simp
    -- Step 7.3: compute the real part of the scalar.
    have hRe' : (↑a / (↑Real.pi * (↑a ^ 2 + ↑v ^ 2) : ℂ)).re = a / (Real.pi * (a ^ 2 + v ^ 2)) := by
      rw [hden]
      have h := Complex.div_ofReal_re (z := (a : ℂ)) (x := (Real.pi * (a ^ 2 + v ^ 2)))
      calc
        (↑a / ((Real.pi * (a ^ 2 + v ^ 2) : ℝ) : ℂ)).re
            = (a : ℂ).re / (Real.pi * (a ^ 2 + v ^ 2)) := by simpa using h
        _ = a / (Real.pi * (a ^ 2 + v ^ 2)) := by simp
    -- Step 7.4: compute the imaginary part of the scalar.
    have hIm' : (↑a / (↑Real.pi * (↑a ^ 2 + ↑v ^ 2) : ℂ)).im = 0 := by
      rw [hden]
      have h := Complex.div_ofReal_im (z := (a : ℂ)) (x := (Real.pi * (a ^ 2 + v ^ 2)))
      calc
        (↑a / ((Real.pi * (a ^ 2 + v ^ 2) : ℝ) : ℂ)).im
            = (a : ℂ).im / (Real.pi * (a ^ 2 + v ^ 2)) := by simpa using h
        _ = 0 := by simp
    -- Step 7.5: substitute and simplify.
    simp [hRe', hIm', mul_comm]

  -- Rewrite `hReEq` using `hReIntegrand`.
  have hReEq' :
      (∫ v : ℝ, (a / (Real.pi * (a ^ 2 + v ^ 2))) * Real.cos v) = Real.exp (-a) := by
    /-
    Step 7.6: Rewrite the integral using the pointwise identity `hReIntegrand`.

    We deliberately use `rw` rather than `simp` here.

    Reason:
    `simp` tries to further simplify the real-part expression by expanding it into
    `cos`/`sin` pieces (`Complex.mul_re` etc.), which would prevent `hReIntegrand` from
    matching syntactically.

    With `rw [← hReIntegrand]`, the goal becomes *exactly* `hReEq`.
    -/
    rw [← hReIntegrand]
    exact hReEq

  /-
  Step 8: Rewrite the integral into the form `(a/π) * ∫ cos v /(a^2+v^2)`.
  -/
  have hFactor :
      (∫ v : ℝ, (a / (Real.pi * (a ^ 2 + v ^ 2))) * Real.cos v)
        = (a / Real.pi) * (∫ v : ℝ, Real.cos v / (a ^ 2 + v ^ 2)) := by
    -- Step 8.1: rewrite the integrand pointwise.
    have hEq : (fun v : ℝ => (a / (Real.pi * (a ^ 2 + v ^ 2))) * Real.cos v)
        = fun v : ℝ => (a / Real.pi) * (Real.cos v / (a ^ 2 + v ^ 2)) := by
      funext v
      field_simp [Real.pi_ne_zero]
    -- Step 8.2: pull out the constant factor `(a/π)`.
    -- (No integrability assumptions are needed for `integral_const_mul` because the Bochner
    -- integral is defined for all functions; still, our functions are integrable anyway.)
    simpa [hEq, mul_assoc] using (integral_const_mul (μ := (volume : Measure ℝ)) (a / Real.pi)
      (fun v : ℝ => Real.cos v / (a ^ 2 + v ^ 2)))

  -- Combine `hReEq'` with `hFactor`.
  have hMain : Real.exp (-a) = (a / Real.pi) * (∫ v : ℝ, Real.cos v / (a ^ 2 + v ^ 2)) := by
    -- `hReEq' : ∫ (...) = exp(-a)`.
    -- So we rewrite the left-hand side using `hFactor` and then flip.
    --
    -- Concretely:
    --   exp(-a) = ∫ ...
    --          = (a/π) * ∫ cos/(a^2+v^2)
    --
    -- Start:
    --
    have := congrArg (fun r : ℝ => r) hReEq'
    -- Turn `∫ (...) = exp(-a)` into `exp(-a) = ∫ (...)`.
    --
    -- Then rewrite the integral via `hFactor`.
    --
    -- (We keep the steps explicit for clarity.)
    --
    -- `hReEq'` is `Integral = exp(-a)`, so take symmetric.
    have h1 : Real.exp (-a) = ∫ v : ℝ, (a / (Real.pi * (a ^ 2 + v ^ 2))) * Real.cos v := by
      simpa using hReEq'.symm
    -- Now substitute the factorization.
    simpa [hFactor] using h1

  /-
  Step 9: Solve for the target integral.
  -/
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hSolved : (∫ v : ℝ, Real.cos v / (a ^ 2 + v ^ 2)) = Real.pi * (Real.exp (-a) / a) := by
    -- This is a purely algebraic rearrangement of `hMain`.
    -- We reuse the pattern verified in `tmp/check_solve_for_I.lean`.
    --
    -- Start from `hMain` and solve.
    --
    -- (We keep the full reasoning explicit.)
    --
    -- Let `I` denote the integral.
    --
    -- Then `hMain` is `exp(-a) = (a/π) * I`.
    --
    -- So `I = π * (exp(-a) / a)`.
    --
    -- Implemented in Lean by multiplying both sides by `π/a` and clearing denominators.
    --
    -- First, rewrite `hMain` into the shape `exp(-a) = (a/π) * I`.
    have h : Real.exp (-a) = (a / Real.pi) * (∫ v : ℝ, Real.cos v / (a ^ 2 + v ^ 2)) := hMain
    -- Apply the generic rearrangement lemma pattern.
    -- (We inline it here.)
    have h' : (Real.pi / a) * Real.exp (-a)
        = (Real.pi / a) * ((a / Real.pi) * (∫ v : ℝ, Real.cos v / (a ^ 2 + v ^ 2))) := by
      simpa [mul_assoc] using congrArg (fun r : ℝ => (Real.pi / a) * r) h
    have h'' : (Real.pi / a) * ((a / Real.pi) * (∫ v : ℝ, Real.cos v / (a ^ 2 + v ^ 2)))
        = (∫ v : ℝ, Real.cos v / (a ^ 2 + v ^ 2)) := by
      field_simp [ha0, Real.pi_ne_zero]
    have : (Real.pi / a) * Real.exp (-a) = (∫ v : ℝ, Real.cos v / (a ^ 2 + v ^ 2)) := by
      simpa [h''] using h'
    -- Rearrange `(π/a) * exp(-a)` into `π * (exp(-a)/a)`.
    -- Also flip the equality to match the goal.
    symm
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using this

  /-
  Step 10: Our original integral has denominator `x^2 + a^2`, not `a^2 + x^2`.
  Use commutativity of addition to rewrite.
  -/
  simpa [add_comm, add_left_comm, add_assoc] using hSolved

/-Informal Statement

Show that $ \int_{-\infty}^{\infty} \frac{\cos x}{x^2 + a^2} dx = \pi \frac{e^{-a}}{a}$ for $a > 0$.
-/

/-Informal Proof

$\cos x=\frac{e^{i x}+e^{-i x}}{2}$. changing $x \rightarrow-x$ we see that we can just integrate $e^{i x} /\left(x^2+a^2\right)$ and we'll get the same answer. Again, we use the same semicircle and part of the real line. The only pole is $x=i a$, it has order 1 and the residue at it is $\lim _{x \rightarrow i a} \frac{e^{i x}}{x^2+a^2}(x-i a)=\frac{e^{-a}}{2 i a}$, which multiplied by $2 \pi i$ gives the answer.
-/

theorem Shakarchi_exercise_3_3 (a : ℝ) (ha : 0 < a) :
    Tendsto (λ y => ∫ x in -y..y, Real.cos x / (x ^ 2 + a ^ 2))
    atTop (𝓝 (Real.pi * (Real.exp (-a) / a))) := by
  /-
  Step 1: Let `g(x) = cos x / (x^2 + a^2)`.
  We will apply `MeasureTheory.intervalIntegral_tendsto_integral` to `g`.
  -/
  let g : ℝ → ℝ := fun x => Real.cos x / (x ^ 2 + a ^ 2)

  /-
  Step 2: Prove `g` is integrable on `ℝ`.
  -/
  have hg_int : Integrable g := by
    simpa [g] using integrable_cos_div_sq_add_sq a ha

  /-
  Step 3: Use the improper-integral lemma `intervalIntegral_tendsto_integral` with
  `a(y) = -y` and `b(y) = y`.
  -/
  have hTendsto : Tendsto (fun y : ℝ => ∫ x in (-y)..y, g x) atTop (𝓝 (∫ x : ℝ, g x)) := by
    -- `(-y)` tends to `-∞` and `y` tends to `+∞`.
    have ha' : Tendsto (fun y : ℝ => -y) atTop atBot := by
      simpa using (tendsto_neg_atTop_atBot)
    have hb' : Tendsto (fun y : ℝ => y) atTop atTop := tendsto_id
    -- Apply the general theorem.
    simpa using (MeasureTheory.intervalIntegral_tendsto_integral (μ := (volume : Measure ℝ))
      (f := g) (a := fun y : ℝ => -y) (b := fun y : ℝ => y) hg_int ha' hb')

  /-
  Step 4: Evaluate the whole-line integral `∫ g`.
  -/
  have hEval : (∫ x : ℝ, g x) = Real.pi * (Real.exp (-a) / a) := by
    -- This is exactly the Fourier-analytic computation proved above.
    simpa [g] using integral_cos_div_sq_add_sq a ha

  /-
  Step 5: Substitute the evaluation into the limit statement.
  -/
  simpa [hEval] using hTendsto
