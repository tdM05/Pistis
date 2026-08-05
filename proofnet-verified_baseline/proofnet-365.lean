import Mathlib

open Complex Filter Function Metric Finset MeasureTheory Real Set
open scoped BigOperators Topology FourierTransform RealInnerProductSpace Complex Interval

noncomputable section

/-!

## Goal (informal)

Prove the *symmetric improper integral* identity

`lim_{y→∞} ∫_{-y}^{y} (x sin x)/(x^2 + a^2) dx = π * exp(-a)` for `a > 0`.

## Strategy (high-level)

This integrand is **not absolutely integrable** on `ℝ` (it behaves like `sin x / x`), so we do
**not** try to interpret it as a Bochner integral over `ℝ`.

Instead, we proceed as follows.

- Step 1: Use **integration by parts on the finite interval** `[-y, y]`.
  This rewrites the integral as:
  - a boundary term that goes to `0`, plus
  - an integral of an **absolutely integrable** function.

- Step 2: Use `MeasureTheory.intervalIntegral_tendsto_integral` on this absolutely integrable
  function to pass to a whole-line integral.

- Step 3: Evaluate the resulting whole-line integral using a Fourier-analytic computation for
  `∫ cos x / (x^2 + a^2)` (proved below), and then a differentiation-under-the-integral lemma
  (from `Analysis/Calculus/ParametricIntegral`) to obtain the companion identity for
  `∫ cos x / (x^2 + a^2)^2`.

No new axioms are introduced.
-/



/-Informal Statement

Show that $ \int_{-\infty}^{\infty} \frac{x \sin x}{x^2 + a^2} dx = \pi e^{-a}$ for $a > 0$.
-/

/-Informal Proof

$$
x /\left(x^2+a^2\right)=x / 2 i a(1 /(x-i a)-1 /(x+i a))=1 / 2 i a(i a /(x-i a)+i a /(x+
$$
$i a))=(1 /(x-i a)+1 /(x+i a)) / 2$. So we care about $\sin (x)(1 /(x-i a)+$ $1 /(x+i a)) / 2$. Its residue at $x=i a$ is $\sin (i a) / 2=\left(e^{-a}-e^a\right) / 4 i$.?
-/

/-!
## Part A: A Fourier-analytic evaluation of `∫ cos x / (x^2 + a^2)`

We reproduce (in a self-contained way) the Fourier-analytic identity

`∫_{ℝ} cos x / (x^2 + a^2) dx = π * (exp(-a) / a)` for `a > 0`.

This will be used later to evaluate the absolutely integrable whole-line integral that appears
after integrating by parts.
-/

/-!
### Helper lemma: a small complex-algebra identity

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
### Integrability lemmas

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
  Step 3: use a scaling change-of-variables lemma.

  The lemma `integrable_comp_mul_left_iff` says integrability is preserved by the map
  `x ↦ R * x` (for `R ≠ 0`). We use the scaling factor `R = 1/a`.
  -/
  have hR : (1 / a) ≠ 0 := by
    simp [ha0]
  have hcomp : Integrable (fun x : ℝ => (1 + (((1 / a) * x) ^ 2))⁻¹) := by
    -- Step 3.1: apply the change-of-variables lemma to `hbase`.
    exact (MeasureTheory.integrable_comp_mul_left_iff
      (g := fun y : ℝ => (1 + y ^ 2)⁻¹) (R := (1 / a)) hR).2 hbase

  /-
  Step 4: relate our target function to the scaled base function.

  We show the pointwise identity
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
### Fourier-analytic computation

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
    /-
    Step 8.1: substitute `Aneg` and `Apos`.
    Step 8.2: use `one_div` and simplify the common factor `2π`.
    Step 8.3: use `inv_add_inv_conj` to compute the remaining sum.
    Step 8.4: finish with `field_simp` to clear denominators.

    We follow the same overall structure as the scratch proof:
    1) simplify constants so only the core rational identity remains,
    2) solve that identity using `inv_add_inv_conj_I_mul`.
    -/

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
    have hCore : ((↑a - Complex.I * ↑w)⁻¹ + ((a : ℂ) + Complex.I * (w : ℂ))⁻¹ : ℂ)
        = (2 * a / (a ^ 2 + w ^ 2) : ℂ) := by
      -- `simp` converts `(a:ℂ) + I*(w:ℂ)` into `↑a + I*↑w`.
      simpa using (inv_add_inv_conj_I_mul a w)

    -- Rewrite the goal using `hNegInv`, then close with `hCore` and a final cast simplification.
    simp [hNegInv]
    rw [hCore]
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
      have hx0 : 0 < x := by simp at hx; exact hx
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
  -/
  have hReIntegrand :
      (fun v : ℝ => (Complex.exp (↑v * Complex.I) * (a / (Real.pi * (a ^ 2 + v ^ 2)) : ℂ)).re)
        = fun v : ℝ => (a / (Real.pi * (a ^ 2 + v ^ 2))) * Real.cos v := by
    funext v
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
    simpa [hEq, mul_assoc] using (integral_const_mul (μ := (volume : Measure ℝ)) (a / Real.pi)
      (fun v : ℝ => Real.cos v / (a ^ 2 + v ^ 2)))

  -- Combine `hReEq'` with `hFactor`.
  have hMain : Real.exp (-a) = (a / Real.pi) * (∫ v : ℝ, Real.cos v / (a ^ 2 + v ^ 2)) := by
    have h1 : Real.exp (-a) = ∫ v : ℝ, (a / (Real.pi * (a ^ 2 + v ^ 2))) * Real.cos v := by
      simpa using hReEq'.symm
    simpa [hFactor] using h1

  /-
  Step 9: Solve for the target integral.
  -/
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hSolved : (∫ v : ℝ, Real.cos v / (a ^ 2 + v ^ 2)) = Real.pi * (Real.exp (-a) / a) := by
    have h : Real.exp (-a) = (a / Real.pi) * (∫ v : ℝ, Real.cos v / (a ^ 2 + v ^ 2)) := hMain
    have h' : (Real.pi / a) * Real.exp (-a)
        = (Real.pi / a) * ((a / Real.pi) * (∫ v : ℝ, Real.cos v / (a ^ 2 + v ^ 2))) := by
      simpa [mul_assoc] using congrArg (fun r : ℝ => (Real.pi / a) * r) h
    have h'' : (Real.pi / a) * ((a / Real.pi) * (∫ v : ℝ, Real.cos v / (a ^ 2 + v ^ 2)))
        = (∫ v : ℝ, Real.cos v / (a ^ 2 + v ^ 2)) := by
      field_simp [ha0, Real.pi_ne_zero]
    have : (Real.pi / a) * Real.exp (-a) = (∫ v : ℝ, Real.cos v / (a ^ 2 + v ^ 2)) := by
      simpa [h''] using h'
    symm
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using this

  /-
  Step 10: Our original integral has denominator `x^2 + a^2`, not `a^2 + x^2`.
  Use commutativity of addition to rewrite.
  -/
  simpa [add_comm, add_left_comm, add_assoc] using hSolved

/-!
## Part B: A companion identity for `∫ cos x / (x^2 + a^2)^2`

This is obtained by differentiating under the integral sign with respect to the parameter `a`.

Key points:
- The integrand `cos x / (x^2 + a^2)` is absolutely integrable, and its derivative in `a`
  decays like `1/x^4`, hence is also absolutely integrable.
- Therefore, we can use `hasDerivAt_integral_of_dominated_loc_of_deriv_le`.
-/

lemma integrable_cos_div_sq_add_sq_sq (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.cos x / (x ^ 2 + a ^ 2) ^ 2) := by
  /-
  Step 1: We dominate `|cos x / (x^2 + a^2)^2|` by a constant multiple of `(x^2 + a^2)⁻¹`.

  The key inequality is `(x^2 + a^2)⁻² ≤ (1/a^2) * (x^2 + a^2)⁻¹`.
  -/
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hInv : Integrable (fun x : ℝ => (x ^ 2 + a ^ 2)⁻¹) := integrable_inv_sq_add_sq a ha

  -- Step 2: use `Integrable.mono'` with a pointwise bound.
  refine Integrable.mono' (hInv.const_mul (c := (1 / a ^ 2))) ?_ ?_
  · /-
    Step 2.1: show the integrand is a.e. strongly measurable.

    We prove it by showing the function is continuous (since the denominator never vanishes when
    `a > 0`), then using `Continuous.aestronglyMeasurable`.
    -/
    have hden_ne : ∀ x : ℝ, (x ^ 2 + a ^ 2) ^ 2 ≠ 0 := by
      intro x
      have hpos : 0 < x ^ 2 + a ^ 2 :=
        add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_pos ha)
      have hpos2 : 0 < (x ^ 2 + a ^ 2) ^ 2 := by
        -- Square of a positive number is positive.
        simpa [pow_two] using mul_pos hpos hpos
      exact ne_of_gt hpos2
    have hcont_num : Continuous (fun x : ℝ => Real.cos x) := by fun_prop
    have hcont_den : Continuous (fun x : ℝ => (x ^ 2 + a ^ 2) ^ 2) := by fun_prop
    have hcont : Continuous (fun x : ℝ => Real.cos x / (x ^ 2 + a ^ 2) ^ 2) :=
      hcont_num.div hcont_den hden_ne
    exact hcont.aestronglyMeasurable
  · /-
    Step 2.2: pointwise bound.

    We show
    `‖cos x / (x^2+a^2)^2‖ ≤ (1/a^2) * (x^2+a^2)⁻¹`.
    -/
    refine MeasureTheory.ae_of_all _ (fun x => ?_)
    -- Reduce norms to abs.
    simp [Real.norm_eq_abs]
    -- Use `|cos x| ≤ 1`.
    have hcos : |Real.cos x| ≤ (1 : ℝ) := abs_cos_le_one x
    -- Use positivity of the denominator.
    have hden_pos : 0 < x ^ 2 + a ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_pos ha)
    have hden_pos2 : 0 < (x ^ 2 + a ^ 2) ^ 2 := by
      -- square of a positive number is positive
      simpa [pow_two] using mul_pos hden_pos hden_pos
    -- `|cos| / (x^2+a^2)^2 ≤ 1 / (x^2+a^2)^2`.
    have h1 : |Real.cos x| / (x ^ 2 + a ^ 2) ^ 2 ≤ (1 : ℝ) / (x ^ 2 + a ^ 2) ^ 2 :=
      div_le_div_of_nonneg_right hcos (le_of_lt hden_pos2)
    -- Next, use `(x^2+a^2)^2 ≥ a^2 * (x^2+a^2)` because `x^2+a^2 ≥ a^2`.
    -- This gives `1/(x^2+a^2)^2 ≤ (1/a^2) * 1/(x^2+a^2)`.
    have hx_ge_a : a ^ 2 ≤ x ^ 2 + a ^ 2 := by
      linarith [sq_nonneg x]
    have h2 : (1 : ℝ) / (x ^ 2 + a ^ 2) ^ 2 ≤ (1 / a ^ 2) * (1 / (x ^ 2 + a ^ 2)) := by
      -- Clear denominators safely.
      have hxa_pos : 0 < x ^ 2 + a ^ 2 := hden_pos
      field_simp [ha0, (ne_of_gt hxa_pos)]
      exact hx_ge_a
    -- Combine the inequalities.
    have h3 : |Real.cos x| / (x ^ 2 + a ^ 2) ^ 2 ≤ (1 / a ^ 2) * (1 / (x ^ 2 + a ^ 2)) :=
      le_trans h1 h2
    -- Finally rewrite `1/(x^2+a^2)` as `(x^2+a^2)⁻¹`.
    simpa [one_div, mul_assoc, mul_left_comm, mul_comm, pow_two] using h3

lemma integral_cos_div_sq_add_sq_sq (a : ℝ) (ha : 0 < a) :
    (∫ x : ℝ, Real.cos x / (x ^ 2 + a ^ 2) ^ 2)
      = Real.pi * Real.exp (-a) * ((a + 1) / (2 * a ^ 3)) := by
  /-
  Step 1: Introduce the parametric integrand `F(a,x) = cos x / (x^2 + a^2)`.
  -/
  let F : ℝ → ℝ → ℝ := fun a x => Real.cos x / (x ^ 2 + a ^ 2)
  let F' : ℝ → ℝ → ℝ := fun a x => (-2 * a) * Real.cos x / (x ^ 2 + a ^ 2) ^ 2

  /-
  Step 2: Apply the library theorem
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le`.
  This gives a formula for the derivative of

  `I(a) = ∫_{ℝ} F(a,x) dx`

  in terms of the integral of `F'`.
  -/
  have ha0 : a ≠ 0 := ne_of_gt ha
  let ε : ℝ := a / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith

  -- Step 2.1: measurability of `F a` for `a` near the base point.
  have hF_meas : ∀ᶠ a' in 𝓝 a, AEStronglyMeasurable (F a') (volume : Measure ℝ) := by
    -- We use `Filter.Eventually.of_forall`:
    -- from a pointwise statement `∀ a', ...` we get an eventual statement near `a`.
    refine (Filter.Eventually.of_forall ?_)
    intro a'
    -- `F a'` is a composition of continuous functions; in particular it is measurable, hence
    -- a.e. strongly measurable.
    fun_prop

  -- Step 2.2: integrability of `F a`.
  have hF_int : Integrable (F a) (volume : Measure ℝ) := by
    -- This is exactly `integrable_cos_div_sq_add_sq`.
    simpa [F] using (integrable_cos_div_sq_add_sq a ha)

  -- Step 2.3: measurability of `F' a`.
  have hF'_meas : AEStronglyMeasurable (F' a) (volume : Measure ℝ) := by
    -- `F' a` is continuous, hence a.e. strongly measurable.
    fun_prop

  -- Step 2.4: provide a uniform bound on `‖F' a' x‖` for `a'` near `a`.
  -- We use the crude bound
  -- `‖F' a' x‖ ≤ (3a) * (x^2 + (a/2)^2)⁻²` on the ball `ball a (a/2)`.
  let bound : ℝ → ℝ := fun x => (3 * a) * (x ^ 2 + (a / 2) ^ 2)⁻¹ * (x ^ 2 + (a / 2) ^ 2)⁻¹
  have hbound_int : Integrable bound (volume : Measure ℝ) := by
    /-
    Step 2.4.1: show integrability of `(x^2 + (a/2)^2)⁻²` by comparing it to `(x^2 + (a/2)^2)⁻¹`.
    -/
    have ha2_pos : 0 < a / 2 := by linarith
    have hInv : Integrable (fun x : ℝ => (x ^ 2 + (a / 2) ^ 2)⁻¹) :=
      integrable_inv_sq_add_sq (a / 2) ha2_pos
    -- Use `((x^2+c^2)⁻¹) ≤ (1/c^2)` to bound the square.
    have hInvSq : Integrable (fun x : ℝ => (x ^ 2 + (a / 2) ^ 2)⁻¹ * (x ^ 2 + (a / 2) ^ 2)⁻¹) := by
      /-
      Step 2.4.1.1: show that the square `(x^2+c^2)⁻¹ * (x^2+c^2)⁻¹` is dominated by a constant
      times the single factor `(x^2+c^2)⁻¹`.

      The key point is the elementary bound

      `(x^2 + c^2)⁻¹ ≤ (c^2)⁻¹`

      which holds since `x^2 + c^2 ≥ c^2 > 0`.
      -/
      have hdom : ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
          ‖(x ^ 2 + (a / 2) ^ 2)⁻¹ * (x ^ 2 + (a / 2) ^ 2)⁻¹‖
            ≤ ((a / 2) ^ 2)⁻¹ * (x ^ 2 + (a / 2) ^ 2)⁻¹ := by
        refine MeasureTheory.ae_of_all _ (fun x => ?_)

        -- Step 2.4.1.1.1: positivity/nonnegativity facts.
        have hpos : 0 < x ^ 2 + (a / 2) ^ 2 :=
          add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_pos ha2_pos)
        have hinv_nonneg : 0 ≤ (x ^ 2 + (a / 2) ^ 2)⁻¹ := inv_nonneg.mpr (le_of_lt hpos)

        -- Step 2.4.1.1.2: bound the inverse by the constant `((a/2)^2)⁻¹`.
        have hle : (x ^ 2 + (a / 2) ^ 2)⁻¹ ≤ ((a / 2) ^ 2)⁻¹ := by
          have hcpos : 0 < (a / 2) ^ 2 := sq_pos_of_pos ha2_pos
          have hxge : (a / 2) ^ 2 ≤ x ^ 2 + (a / 2) ^ 2 := by linarith [sq_nonneg x]
          -- `inv_le_inv₀` is the standard monotonicity lemma for inversion on positive numbers.
          exact (inv_le_inv₀ hpos hcpos).2 hxge

        -- Step 2.4.1.1.3: multiply the inequality by the nonnegative factor `(x^2+(a/2)^2)⁻¹`.
        have hmul : (x ^ 2 + (a / 2) ^ 2)⁻¹ * (x ^ 2 + (a / 2) ^ 2)⁻¹
            ≤ ((a / 2) ^ 2)⁻¹ * (x ^ 2 + (a / 2) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hle hinv_nonneg

        -- Step 2.4.1.1.4: rewrite norms as absolute values and remove the absolute value of a nonnegative.
        have hmul_nonneg : 0 ≤ (x ^ 2 + (a / 2) ^ 2)⁻¹ * (x ^ 2 + (a / 2) ^ 2)⁻¹ :=
          mul_nonneg hinv_nonneg hinv_nonneg
        -- The goal is `‖inv*inv‖ ≤ ...`. Since `inv*inv ≥ 0`, the norm is just `inv*inv`.
        have hden_nonneg : 0 ≤ x ^ 2 + (a / 2) ^ 2 :=
          add_nonneg (sq_nonneg x) (sq_nonneg (a / 2))
        simpa [Real.norm_eq_abs, abs_of_nonneg hmul_nonneg, abs_of_nonneg hden_nonneg] using hmul

      /-
      Step 2.4.1.2: use `Integrable.mono'` with the dominating integrable function
      `x ↦ ((a/2)^2)⁻¹ * (x^2 + (a/2)^2)⁻¹`.
      -/
      refine Integrable.mono' (hInv.const_mul (c := ((a / 2) ^ 2)⁻¹)) (by fun_prop) ?_
      exact hdom
    -- Finally multiply by the constant `3a`.
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using hInvSq.const_mul (c := (3 * a))

  have h_bound : ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
      ∀ a' ∈ ball a ε, ‖F' a' x‖ ≤ bound x := by
    refine MeasureTheory.ae_of_all _ (fun x => ?_)
    intro a' ha'
    -- From `a' ∈ ball a (a/2)`, we get `|a' - a| < a/2` hence `a/2 < a'` and `a' < 3a/2`.
    have ha'_lt : a' < a + ε := by
      have : dist a' a < ε := by simpa [Metric.mem_ball, dist_eq_norm] using ha'
      -- `dist` on `ℝ` is `|a' - a|`.
      have : |a' - a| < ε := by simpa [Real.dist_eq] using this
      -- Rearrange.
      have : a' - a < ε := lt_of_abs_lt this
      linarith
    have ha'_gt : a - ε < a' := by
      have : dist a' a < ε := by simpa [Metric.mem_ball, dist_eq_norm] using ha'
      have : |a' - a| < ε := by simpa [Real.dist_eq] using this
      have : -(ε : ℝ) < a' - a := neg_lt_of_abs_lt this
      linarith
    have ha'_pos : 0 < a' := by
      -- `a' > a - a/2 = a/2 > 0`.
      dsimp [ε] at ha'_gt
      linarith
    have ha'_abs_le : |a'| ≤ (3 * a) / 2 := by
      have : a' ≤ (3 * a) / 2 := by
        -- `a' < a + a/2 = 3a/2`.
        dsimp [ε] at ha'_lt
        linarith
      have ha'_nonneg : 0 ≤ a' := le_of_lt ha'_pos
      simpa [abs_of_nonneg ha'_nonneg] using this

    -- Now bound `‖F' a' x‖`.
    -- Start by expanding the definition.
    have : ‖F' a' x‖ ≤ (3 * a) * (x ^ 2 + (a / 2) ^ 2)⁻¹ * (x ^ 2 + (a / 2) ^ 2)⁻¹ := by
      /-
      Step 2.4.2 (core estimate): we prove the uniform bound

      `‖F' a' x‖ ≤ (3a) * (x^2 + (a/2)^2)⁻¹ * (x^2 + (a/2)^2)⁻¹`.

      The proof is a “three-factor” domination:
      1. rewrite `‖F' a' x‖` as a product involving `|a'|`, `|cos x|`, and two inverse factors;
      2. bound `|cos x| ≤ 1`;
      3. bound `2*|a'| ≤ 3*a` using `a' ∈ ball a (a/2)`;
      4. compare inverse factors using monotonicity of `t ↦ t⁻¹` on positive reals.
      -/

      -- Step 2.4.2.1: a small helper lemma for simp.
      -- We want to eliminate absolute values of the denominator `x^2 + a'^2`.
      -- Since it is a sum of squares, it is always nonnegative.
      have hnonnegDen : 0 ≤ x * x + a' * a' := by
        nlinarith [sq_nonneg x, sq_nonneg a']

      -- Step 2.4.2.2: rewrite **only the left-hand side** into a product form.
      -- We deliberately avoid rewriting the whole goal with `simp`, since that would also
      -- unfold/simplify the right-hand side into a less readable expression.
      have hRewrite :
          ‖F' a' x‖ = (2 * |a'|) * |Real.cos x| * ((x ^ 2 + a' ^ 2)⁻¹ * (x ^ 2 + a' ^ 2)⁻¹) := by
        -- This is a straightforward normalization of the expression:
        -- * `‖·‖` becomes `|·|` on `ℝ`,
        -- * `/ ( ... )^2` becomes `* ((... )⁻¹ * (... )⁻¹)`.
        -- The hypothesis `hnonnegDen` is used to remove an absolute value around the nonnegative
        -- quantity `x^2 + a'^2`.
        simp [F', Real.norm_eq_abs, div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm,
          abs_of_nonneg hnonnegDen]

      -- Use the rewrite lemma to replace the original goal.
      rw [hRewrite]

      -- Step 2.4.2.3: bound the cosine factor.
      have hcos : |Real.cos x| ≤ (1 : ℝ) := abs_cos_le_one x

      -- Step 2.4.2.4: compare `x^2 + (a/2)^2` and `x^2 + a'^2`.
      have hden_ge : x ^ 2 + (a / 2) ^ 2 ≤ x ^ 2 + a' ^ 2 := by
        -- It suffices to show `(a/2)^2 ≤ a'^2`, then add `x^2` to both sides.
        have : (a / 2) ^ 2 ≤ a' ^ 2 := by
          -- From `a' ∈ ball a (a/2)` we derived `a/2 ≤ a'` earlier.
          have h : a / 2 ≤ a' := by
            dsimp [ε] at ha'_gt
            linarith
          -- Convert `a/2 ≤ a'` into an inequality between absolute values, then apply `sq_le_sq`.
          have ha2_nonneg : 0 ≤ a / 2 := by linarith [ha]
          have ha'_nonneg : 0 ≤ a' := le_of_lt ha'_pos
          have habs : |a / 2| ≤ |a'| := by
            simpa [abs_of_nonneg ha2_nonneg, abs_of_nonneg ha'_nonneg] using h
          exact (sq_le_sq).2 habs
        linarith

      -- Step 2.4.2.5: turn this into an inequality between inverse *products*.
      have hInv : (x ^ 2 + a' ^ 2)⁻¹ * (x ^ 2 + a' ^ 2)⁻¹
          ≤ (x ^ 2 + (a / 2) ^ 2)⁻¹ * (x ^ 2 + (a / 2) ^ 2)⁻¹ := by
        -- Step 2.4.2.5.1: inverse is order-reversing on positive reals.
        have hpos1 : 0 < x ^ 2 + (a / 2) ^ 2 :=
          add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_pos (by linarith [ha]))
        have hpos2 : 0 < x ^ 2 + a' ^ 2 :=
          add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_pos ha'_pos)
        have hinv : (x ^ 2 + a' ^ 2)⁻¹ ≤ (x ^ 2 + (a / 2) ^ 2)⁻¹ := by
          -- This is exactly `inv_le_inv₀` applied to the inequality `x^2+(a/2)^2 ≤ x^2+a'^2`.
          exact (inv_le_inv₀ hpos2 hpos1).2 hden_ge

        -- Step 2.4.2.5.2: upgrade `invLarge ≤ invSmall` to `invLarge*invLarge ≤ invSmall*invSmall`.
        -- We do this in two monotonicity steps.
        have hinvLarge_nonneg : 0 ≤ (x ^ 2 + a' ^ 2)⁻¹ := inv_nonneg.mpr (le_of_lt hpos2)
        have hinvSmall_nonneg : 0 ≤ (x ^ 2 + (a / 2) ^ 2)⁻¹ :=
          inv_nonneg.mpr (add_nonneg (sq_nonneg x) (sq_nonneg (a / 2)))
        have h1 : (x ^ 2 + a' ^ 2)⁻¹ * (x ^ 2 + a' ^ 2)⁻¹ ≤ (x ^ 2 + a' ^ 2)⁻¹ * (x ^ 2 + (a / 2) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left hinv hinvLarge_nonneg
        have h2 : (x ^ 2 + a' ^ 2)⁻¹ * (x ^ 2 + (a / 2) ^ 2)⁻¹ ≤ (x ^ 2 + (a / 2) ^ 2)⁻¹ * (x ^ 2 + (a / 2) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hinv hinvSmall_nonneg
        exact le_trans h1 h2

      -- Step 2.4.2.6: nonnegativity of the inverse-product factor, used for `mul_le_mul`.
      have hInv_nonneg : 0 ≤ (x ^ 2 + a' ^ 2)⁻¹ * (x ^ 2 + a' ^ 2)⁻¹ := by
        have hden_nonneg : 0 ≤ x ^ 2 + a' ^ 2 := add_nonneg (sq_nonneg x) (sq_nonneg a')
        have hinv_nonneg : 0 ≤ (x ^ 2 + a' ^ 2)⁻¹ := inv_nonneg.mpr hden_nonneg
        exact mul_nonneg hinv_nonneg hinv_nonneg

      -- Step 2.4.2.7: bound the coefficient `2*|a'|` by `3*a`.
      have haCoeff : (2 * |a'| : ℝ) ≤ 3 * a := by
        have := ha'_abs_le
        linarith

      -- Step 2.4.2.8: put the three bounds together.
      calc
        (2 * |a'|) * |Real.cos x| * ((x ^ 2 + a' ^ 2)⁻¹ * (x ^ 2 + a' ^ 2)⁻¹)
            ≤ (2 * |a'|) * 1 * ((x ^ 2 + a' ^ 2)⁻¹ * (x ^ 2 + a' ^ 2)⁻¹) := by
              -- First control the factor `|cos x| ≤ 1`, then multiply by the nonnegative inverse-product.
              have ha_nonneg : 0 ≤ (2 * |a'| : ℝ) := by nlinarith [abs_nonneg a']
              have h1 : (2 * |a'|) * |Real.cos x| ≤ (2 * |a'|) * 1 :=
                mul_le_mul_of_nonneg_left hcos ha_nonneg
              have := mul_le_mul_of_nonneg_right h1 hInv_nonneg
              simpa [mul_assoc, mul_left_comm, mul_comm] using this
        _ ≤ (3 * a) * 1 * ((x ^ 2 + a' ^ 2)⁻¹ * (x ^ 2 + a' ^ 2)⁻¹) := by
              -- Next control the coefficient `2*|a'| ≤ 3*a`, and multiply by the same nonnegative factor.
              have h2 : (2 * |a'|) * 1 ≤ (3 * a) * 1 := by
                -- multiply by `1` does not change the inequality, but keeps the expressions aligned.
                simpa using (mul_le_mul_of_nonneg_right haCoeff (show 0 ≤ (1 : ℝ) from by simp))
              have := mul_le_mul_of_nonneg_right h2 hInv_nonneg
              simpa [mul_assoc, mul_left_comm, mul_comm] using this
        _ ≤ (3 * a) * 1 * ((x ^ 2 + (a / 2) ^ 2)⁻¹ * (x ^ 2 + (a / 2) ^ 2)⁻¹) := by
              -- Finally replace the inverse-product by the larger (more conservative) inverse-product.
              have hcoef_nonneg : 0 ≤ (3 * a : ℝ) * 1 := by nlinarith [le_of_lt ha]
              have := mul_le_mul_of_nonneg_left hInv hcoef_nonneg
              simpa [mul_assoc, mul_left_comm, mul_comm] using this
        _ = (3 * a) * (x ^ 2 + (a / 2) ^ 2)⁻¹ * (x ^ 2 + (a / 2) ^ 2)⁻¹ := by
              -- Remove the harmless `* 1` and reassociate.
              simp [mul_assoc, mul_left_comm, mul_comm]

    -- Finish by rewriting `bound`.
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using this

  -- Step 2.5: show pointwise differentiability in the parameter.
  have h_diff : ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
      ∀ a' ∈ ball a ε, HasDerivAt (fun t : ℝ => F t x) (F' a' x) a' := by
    refine MeasureTheory.ae_of_all _ (fun x => ?_)
    intro a' ha'
    -- The function `t ↦ F t x` is a quotient of differentiable functions.
    -- We compute the derivative explicitly.
    have ha'_pos : 0 < a' := by
      -- same reasoning as above: `a' > a/2 > 0`.
      have : dist a' a < ε := by simpa [Metric.mem_ball, dist_eq_norm] using ha'
      have : |a' - a| < ε := by simpa [Real.dist_eq] using this
      have h : a - ε < a' := by
        have : -(ε : ℝ) < a' - a := neg_lt_of_abs_lt this
        linarith
      dsimp [ε] at h
      linarith
    have ha'_ne : a' ≠ 0 := ne_of_gt ha'_pos
    -- Numerator is constant in `t`.
    have hnum : HasDerivAt (fun t : ℝ => Real.cos x) 0 a' := by
      simpa using (hasDerivAt_const a' (Real.cos x))
    -- Denominator is `x^2 + t^2`.
    have hden : HasDerivAt (fun t : ℝ => x ^ 2 + t ^ 2) (2 * a') a' := by
      -- derivative of `x^2` is `0`, derivative of `t^2` is `2t`.
      have : HasDerivAt (fun t : ℝ => t ^ 2) (2 * a') a' := by
        simpa using (hasDerivAt_pow 2 a')
      -- Add the constant `x^2`.
      simpa [add_comm, add_left_comm, add_assoc] using this.const_add (x ^ 2)
    have hden_ne : (x ^ 2 + a' ^ 2) ≠ 0 := by
      have : 0 < x ^ 2 + a' ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_ne_zero ha'_ne)
      exact ne_of_gt this
    -- Apply the quotient rule.
    have hquot : HasDerivAt (fun t : ℝ => Real.cos x / (x ^ 2 + t ^ 2))
        (((0 * (x ^ 2 + a' ^ 2) - Real.cos x * (2 * a')) / (x ^ 2 + a' ^ 2) ^ 2)) a' := by
      simpa using (hnum.div hden hden_ne)
    -- Simplify the derivative expression to match `F'`.
    -- (This is purely algebra.)
    --
    -- Note: `F' a' x = (-2*a') * cos x / (x^2 + a'^2)^2`.
    --
    have : (-(Real.cos x * (2 * a')) / (x ^ 2 + a' ^ 2) ^ 2)
        = (-2 * a') * Real.cos x / (x ^ 2 + a' ^ 2) ^ 2 := by
      -- Step 2.5.1: reorder the multiplication inside the numerator.
      -- The library gives `-(cos x * (2*a'))`; we want `(-2*a') * cos x`.
      simp [mul_assoc, mul_comm]
    -- Rewrite and finish.
    -- We first let `simp` reduce the quotient-rule derivative to the form `-(cos x * (2*a')) / ...`,
    -- then we apply the algebraic rewrite above.
    simpa [F, F', sub_eq_add_neg, this] using hquot

  -- Step 2.6: assemble the derivative theorem.
  have hI_deriv : HasDerivAt (fun a0 : ℝ => ∫ x : ℝ, F a0 x) (∫ x : ℝ, F' a x) a := by
    -- Apply the library theorem.
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := (volume : Measure ℝ)) (F := F) (x₀ := a) (s := ball a ε) (bound := bound)
      (ball_mem_nhds a hε) hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2

  /-
  Step 3: Compute the derivative of the *closed form* `J(a) = π * exp(-a) / a`.
  -/
  have hJ_deriv : HasDerivAt (fun a0 : ℝ => Real.pi * (Real.exp (-a0) / a0))
      (-Real.pi * Real.exp (-a) * ((a + 1) / a ^ 2)) a := by
    -- We compute this derivative using standard calculus rules.
    --
    -- Step 3.1: derivative of `a ↦ exp(-a)`.
    have hexp : HasDerivAt (fun a0 : ℝ => Real.exp (-a0)) (-Real.exp (-a)) a := by
      -- `exp` derivative is `exp`, then chain rule with `-a`.
      simpa using (Real.hasDerivAt_exp (-a)).comp a (hasDerivAt_neg a)
    -- Step 3.2: derivative of `a ↦ a`.
    have hid : HasDerivAt (fun a0 : ℝ => a0) 1 a := by
      simpa using (hasDerivAt_id a)
    -- Step 3.3: quotient rule for `exp(-a)/a`.
    have hdiv : HasDerivAt (fun a0 : ℝ => Real.exp (-a0) / a0)
        (((-Real.exp (-a)) * a - Real.exp (-a) * 1) / a ^ 2) a := by
      simpa using (hexp.div hid ha0)
    -- Step 3.4: multiply by the constant `π`.
    have hmul : HasDerivAt (fun a0 : ℝ => Real.pi * (Real.exp (-a0) / a0))
        (Real.pi * (((-Real.exp (-a)) * a - Real.exp (-a) * 1) / a ^ 2)) a := by
      -- We use the specialized lemma for multiplying a differentiable function by a constant.
      -- This avoids having to simplify the product-rule output (`0 * ... + π * ...`).
      simpa [mul_assoc] using hdiv.const_mul Real.pi
    -- Step 3.5: simplify the derivative expression.
    -- `(((-exp)*a - exp*1)/a^2)` becomes `-exp * ((a+1)/a^2)`.
    have :
        Real.pi * (((-Real.exp (-a)) * a - Real.exp (-a) * 1) / a ^ 2)
          = -Real.pi * Real.exp (-a) * ((a + 1) / a ^ 2) := by
      field_simp [ha0]
      ring
    -- Transport the derivative value using `HasDerivAt.congr_deriv`.
    exact hmul.congr_deriv this

  /-
  Step 4: Use the fact that the integral function and the closed form agree on a neighborhood
  of `a` (because `a > 0`). Therefore they have the same derivative at `a`.
  -/
  have hEq_near : (fun a0 : ℝ => ∫ x : ℝ, F a0 x)
      =ᶠ[𝓝 a] (fun a0 : ℝ => Real.pi * (Real.exp (-a0) / a0)) := by
    -- Use the neighborhood `ball a (a/2)`, which is contained in the positive reals.
    have hBall : ∀ᶠ a0 in 𝓝 a, a0 ∈ ball a ε := by
      simpa [ε] using (ball_mem_nhds a hε)
    refine hBall.mono ?_
    intro a0 ha0'
    -- From `a0 ∈ ball a (a/2)` we get `0 < a0`.
    have ha0_pos : 0 < a0 := by
      have : dist a0 a < ε := by simpa [Metric.mem_ball, dist_eq_norm] using ha0'
      have : |a0 - a| < ε := by simpa [Real.dist_eq] using this
      have : a - ε < a0 := by
        have : -(ε : ℝ) < a0 - a := neg_lt_of_abs_lt this
        linarith
      dsimp [ε] at this
      linarith
    -- Now apply the previously proved whole-line integral formula.
    simpa [F] using (integral_cos_div_sq_add_sq a0 ha0_pos)

  -- Transfer `hJ_deriv` to a `HasDerivAt` statement about the integral function.
  have hI_deriv_closed : HasDerivAt (fun a0 : ℝ => ∫ x : ℝ, F a0 x)
      (-Real.pi * Real.exp (-a) * ((a + 1) / a ^ 2)) a := by
    -- We use the lemma `HasDerivAt.congr_of_eventuallyEq`.
    -- It says: if two functions are eventually equal in a neighborhood of `a`,
    -- then a derivative statement for one transfers to the other.
    -- Here `hEq_near : I =ᶠ[𝓝 a] J`, and `hJ_deriv` is a derivative statement for `J`.
    -- So we transfer the derivative from `J` to `I` using the eventual equality.
    exact hJ_deriv.congr_of_eventuallyEq hEq_near

  -- Now use uniqueness of derivatives to identify the integral of `F'`.
  have hDerivEq : (∫ x : ℝ, F' a x) = -Real.pi * Real.exp (-a) * ((a + 1) / a ^ 2) := by
    exact (hI_deriv.unique hI_deriv_closed)

  /-
  Step 5: Rewrite `∫ F' a` as `(-2a) * ∫ cos/(x^2+a^2)^2`, then solve.
  -/
  have hFactor : (∫ x : ℝ, F' a x) = (-2 * a) * (∫ x : ℝ, Real.cos x / (x ^ 2 + a ^ 2) ^ 2) := by
    -- Pull out the constant factor `(-2*a)`.
    have hEq : (fun x : ℝ => F' a x) = fun x : ℝ => (-2 * a) * (Real.cos x / (x ^ 2 + a ^ 2) ^ 2) := by
      funext x
      -- Step 5.1: unfold `F'` and normalize the division/multiplication structure.
      -- The left-hand side is `(-2*a*cos x) / (...)^2`.
      -- The right-hand side is `(-2*a) * (cos x / (...)^2)`.
      -- These are equal by associativity of multiplication.
      simp [F', div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    simpa [hEq, mul_assoc] using
      (integral_const_mul (μ := (volume : Measure ℝ)) (-2 * a) (fun x : ℝ => Real.cos x / (x ^ 2 + a ^ 2) ^ 2))

  -- Combine `hDerivEq` and `hFactor` and solve for the desired integral.
  have hK2 : (∫ x : ℝ, Real.cos x / (x ^ 2 + a ^ 2) ^ 2)
      = Real.pi * Real.exp (-a) * ((a + 1) / (2 * a ^ 3)) := by
    -- Start from `hDerivEq`, rewrite the left-hand side using `hFactor`, then clear denominators.
    have : (-2 * a) * (∫ x : ℝ, Real.cos x / (x ^ 2 + a ^ 2) ^ 2)
        = -Real.pi * Real.exp (-a) * ((a + 1) / a ^ 2) := by
      -- `hDerivEq` gives `(∫ F' a) = ...`.
      -- Replace `(∫ F' a)` by `(-2a) * ...`.
      simpa [hFactor] using hDerivEq
    -- Divide both sides by `(-2a)`.
    -- We use `field_simp` with the hypothesis `a ≠ 0`.
    have ha2 : (-2 * a : ℝ) ≠ 0 := by nlinarith [ha0]
    -- Solve:
    -- `(-2a) * K2 = RHS`  ⇒  `K2 = RHS / (-2a)`.
    -- Then rewrite into the requested form.
    calc
      (∫ x : ℝ, Real.cos x / (x ^ 2 + a ^ 2) ^ 2)
          = (-Real.pi * Real.exp (-a) * ((a + 1) / a ^ 2)) / (-2 * a) := by
                -- Use `eq_div_iff` to divide the identity `this` by `(-2*a)`.
                apply (eq_div_iff ha2).2
                -- Goal: `K2 * (-2*a) = RHS`, which follows from `this` by commutativity.
                simpa [mul_comm, mul_left_comm, mul_assoc] using this
      _ = Real.pi * Real.exp (-a) * ((a + 1) / (2 * a ^ 3)) := by
            field_simp [ha0]
  exact hK2


/-!
## Part C: The target limit

We now prove the statement of the exercise.

Key move:
`∫_{-y}^{y} x sin x/(x^2+a^2)` is rewritten by integration by parts into a boundary term
that tends to `0` plus an absolutely integrable integral that converges to a whole-line integral.
-/

theorem Shakarchi_exercise_3_4 (a : ℝ) (ha : 0 < a) :
    Tendsto (λ y => ∫ x in -y..y, x * Real.sin x / (x ^ 2 + a ^ 2))
    atTop (𝓝 (Real.pi * (Real.exp (-a)))) := by
  /-
  Step 1: Define the two functions used in the integration-by-parts step.

  We choose
  - `u(x) = -x / (x^2 + a^2)`
  - `v(x) = cos x`

  so that `v'(x) = -sin x` and therefore `u(x) * v'(x) = x * sin x / (x^2 + a^2)`.
  -/
  let u : ℝ → ℝ := fun x => -x / (x ^ 2 + a ^ 2)
  let u' : ℝ → ℝ := fun x => (x ^ 2 - a ^ 2) / (x ^ 2 + a ^ 2) ^ 2
  let v : ℝ → ℝ := fun x => Real.cos x
  let v' : ℝ → ℝ := fun x => -Real.sin x

  /-
  Step 2: Prove the `HasDerivAt` facts needed for integration by parts.
  -/
  have ha0 : a ≠ 0 := ne_of_gt ha

  have hu : ∀ x ∈ [[(0 : ℝ), 0]], True := by
    intro x hx
    trivial

  have hu_deriv : ∀ x : ℝ, HasDerivAt u (u' x) x := by
    intro x
    /-
    We compute the derivative of `u(x) = -(x)/(x^2+a^2)`.

    Step 2.1: derivative of the numerator `-(x)` is `-1`.
    Step 2.2: derivative of the denominator `(x^2 + a^2)` is `2x`.
    Step 2.3: apply the quotient rule and simplify.
    -/
    have hnum : HasDerivAt (fun x : ℝ => -x) (-1) x := by
      simpa using (hasDerivAt_neg x)
    have hden : HasDerivAt (fun x : ℝ => x ^ 2 + a ^ 2) (2 * x) x := by
      -- derivative of `x^2` is `2x`, constant term has derivative `0`.
      simpa using ((hasDerivAt_pow 2 x).add_const (a ^ 2))
    have hden_ne : x ^ 2 + a ^ 2 ≠ 0 := by
      have : 0 < x ^ 2 + a ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_pos ha)
      exact ne_of_gt this
    have hquot : HasDerivAt (fun x : ℝ => (-x) / (x ^ 2 + a ^ 2))
        (((-1) * (x ^ 2 + a ^ 2) - (-x) * (2 * x)) / (x ^ 2 + a ^ 2) ^ 2) x := by
      -- Apply the quotient rule directly (we avoid `simpa` to keep the derivative expression stable).
      exact (hnum.div hden hden_ne)
    -- Simplify the algebra to match `u'`.
    -- The derivative expression coming from the quotient rule simplifies to
    -- `(-a^2 - x^2 + x*(2*x)) / (x^2+a^2)^2`, which is equal to `(x^2 - a^2)/(x^2+a^2)^2`.
    have hderiv_simp :
        (-a ^ 2 + -x ^ 2 + x * (2 * x)) / (x ^ 2 + a ^ 2) ^ 2
          = (x ^ 2 - a ^ 2) / (x ^ 2 + a ^ 2) ^ 2 := by
      ring
    simpa [u, u', hderiv_simp] using hquot

  have hv_deriv : ∀ x : ℝ, HasDerivAt v (v' x) x := by
    intro x
    -- `d/dx cos x = -sin x`.
    simpa [v, v'] using (Real.hasDerivAt_cos x)

  /-
  Step 3: Use the integration-by-parts lemma on the interval `[-y, y]`.

  We will first produce a pointwise identity valid for each `y`, then take limits.
  -/
  have hParts : ∀ y : ℝ,
      (∫ x in -y..y, x * Real.sin x / (x ^ 2 + a ^ 2))
        = (-2 * y * Real.cos y) / (y ^ 2 + a ^ 2)
          + ∫ x in -y..y, Real.cos x * (a ^ 2 - x ^ 2) / (x ^ 2 + a ^ 2) ^ 2 := by
    intro y
    /-
    Step 3.1: Apply `intervalIntegral.integral_mul_deriv_eq_deriv_mul`.
    -/
    have hIP :
        (∫ x in -y..y, u x * v' x)
          = u y * v y - u (-y) * v (-y) - ∫ x in -y..y, u' x * v x := by
      -- The theorem needs `HasDerivAt` hypotheses on the closed interval; our functions are globally differentiable.
      refine intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (a := -y) (b := y) (u := u) (v := v) (u' := u') (v' := v')
        (hu := ?_) (hv := ?_) (hu' := ?_) (hv' := ?_)
      · intro x hx
        exact hu_deriv x
      · intro x hx
        exact hv_deriv x
      · -- `u'` is continuous hence interval integrable on a compact interval.
        have : Continuous u' := by
          -- rational function with non-vanishing denominator
          have hden_ne : ∀ x : ℝ, (x ^ 2 + a ^ 2) ^ 2 ≠ 0 := by
            intro x
            have : 0 < (x ^ 2 + a ^ 2) ^ 2 := by
              have hpos : 0 < x ^ 2 + a ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_pos ha)
              simpa [pow_two] using mul_pos hpos hpos
            exact ne_of_gt this
          have hcont_num : Continuous fun x : ℝ => x ^ 2 - a ^ 2 := by fun_prop
          have hcont_den : Continuous fun x : ℝ => (x ^ 2 + a ^ 2) ^ 2 := by fun_prop
          -- `u' = num / den`.
          simpa [u'] using (hcont_num.div hcont_den hden_ne)
        exact this.intervalIntegrable _ _
      · -- `v'` is continuous hence interval integrable.
        have : Continuous v' := by
          simpa [v'] using (by fun_prop : Continuous fun x : ℝ => -Real.sin x)
        exact this.intervalIntegrable _ _

    /-
    Step 3.2: Simplify the identity `hIP`.

    We rewrite:
    - `u x * v' x` into the original integrand,
    - the boundary term into `(-2*y*cos y)/(y^2+a^2)`,
    - `-(u' x * v x)` into `cos x * (a^2 - x^2)/(x^2+a^2)^2`.
    -/
    -- Left-hand side simplification.
    have hLHS : (fun x : ℝ => u x * v' x) = fun x : ℝ => x * Real.sin x / (x ^ 2 + a ^ 2) := by
      funext x
      simp [u, v', mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
    -- Boundary term simplification.
    have hBoundary : u y * v y - u (-y) * v (-y) = (-2 * y * Real.cos y) / (y ^ 2 + a ^ 2) := by
      simp [u, v, Real.cos_neg, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg, div_eq_mul_inv]
      ring
    -- Integral term simplification.
    have hInner : (fun x : ℝ => -(u' x * v x))
        = fun x : ℝ => Real.cos x * (a ^ 2 - x ^ 2) / (x ^ 2 + a ^ 2) ^ 2 := by
      funext x
      simp [u', v]
      ring

    -- Put everything together.
    -- Start from `hIP`, rewrite LHS and RHS pieces, then rearrange.
    calc
      (∫ x in -y..y, x * Real.sin x / (x ^ 2 + a ^ 2))
          = (∫ x in -y..y, u x * v' x) := by
                -- rewrite using `hLHS`
                simp [hLHS]
      _ = u y * v y - u (-y) * v (-y) - ∫ x in -y..y, u' x * v x := hIP
      _ = (-2 * y * Real.cos y) / (y ^ 2 + a ^ 2) + ∫ x in -y..y, Real.cos x * (a ^ 2 - x ^ 2) / (x ^ 2 + a ^ 2) ^ 2 := by
            -- rewrite boundary and rewrite the integral as an addition
            --
            -- `A - ∫ B = A + (-(∫ B))` and then `-(∫ B) = ∫ (-B)`.
            --
            -- Finally, rewrite `-B` pointwise using `hInner`.
            have hnegInt :
                -(∫ x in -y..y, u' x * v x) = ∫ x in -y..y, -(u' x * v x) := by
              -- This is just `intervalIntegral.integral_neg` rewritten.
              simp [intervalIntegral.integral_neg (μ := (volume : Measure ℝ))
                  (a := -y) (b := y) (f := fun x : ℝ => u' x * v x)]
            have hcongr : (∫ x in -y..y, -(u' x * v x))
                = ∫ x in -y..y, Real.cos x * (a ^ 2 - x ^ 2) / (x ^ 2 + a ^ 2) ^ 2 := by
              -- `intervalIntegral` is linear, so we can use `integral_congr`.
              refine intervalIntegral.integral_congr ?_
              intro x hx
              -- Rewrite by the pointwise identity `hInner`.
              simpa using (congrArg (fun f : ℝ → ℝ => f x) hInner)
            -- Now substitute both rewrites.
            simp [hBoundary, sub_eq_add_neg, hnegInt, hcongr, add_comm]

  /-
  Step 4: Show the boundary term tends to `0`.
  -/
  have hBoundary_tendsto : Tendsto (fun y : ℝ => (-2 * y * Real.cos y) / (y ^ 2 + a ^ 2)) atTop (𝓝 (0 : ℝ)) := by
    /-
    We bound the norm:

    `‖(-2*y*cos y)/(y^2+a^2)‖ ≤ 2 * y⁻¹` eventually.
    Then `2*y⁻¹ → 0` and we conclude by `squeeze_zero_norm'`.
    -/
    have h_le : ∀ᶠ y : ℝ in atTop, ‖(-2 * y * Real.cos y) / (y ^ 2 + a ^ 2)‖ ≤ (2 : ℝ) * y⁻¹ := by
      -- Eventually `y ≥ 1`, hence `y > 0`. On that tail we bound the expression by `2 / y`.
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
      have hy_pos : 0 < y := lt_of_lt_of_le (by norm_num) hy
      have hy_nonneg : 0 ≤ y := le_of_lt hy_pos
      have hy2_pos : 0 < y ^ 2 := sq_pos_of_pos hy_pos
      have hden_ge : y ^ 2 ≤ y ^ 2 + a ^ 2 := by nlinarith [sq_nonneg a]
      have hden_pos : 0 < y ^ 2 + a ^ 2 := lt_of_lt_of_le hy2_pos hden_ge

      -- Step 4.1: bound the numerator `| -2*y*cos y | ≤ 2*y`.
      have hnum : |(-2 * y * Real.cos y)| ≤ 2 * y := by
        have habs : |(-2 * y * Real.cos y)| = 2 * y * |Real.cos y| := by
          simp [abs_mul, hy_nonneg, mul_assoc, mul_comm]
        calc
          |(-2 * y * Real.cos y)| = 2 * y * |Real.cos y| := habs
          _ ≤ 2 * y * 1 := by
                -- `|cos y| ≤ 1` and `0 ≤ 2*y`.
                have hcos : |Real.cos y| ≤ (1 : ℝ) := abs_cos_le_one y
                have h2y : 0 ≤ 2 * y := by nlinarith [hy_nonneg]
                exact mul_le_mul_of_nonneg_left hcos h2y
          _ = 2 * y := by ring

      -- Step 4.2: now bound the whole quotient.
      calc
        ‖(-2 * y * Real.cos y) / (y ^ 2 + a ^ 2)‖
            = |(-2 * y * Real.cos y) / (y ^ 2 + a ^ 2)| := by
                -- For real numbers, the norm is the absolute value.
                exact Real.norm_eq_abs _
        _ = |(-2 * y * Real.cos y)| / |y ^ 2 + a ^ 2| := by
              simp [abs_div]
        _ = |(-2 * y * Real.cos y)| / (y ^ 2 + a ^ 2) := by
              simp [abs_of_pos hden_pos]
        _ ≤ (2 * y) / (y ^ 2 + a ^ 2) := by
              exact div_le_div_of_nonneg_right hnum (le_of_lt hden_pos)
        _ ≤ (2 * y) / (y ^ 2) := by
              -- Since `y^2 ≤ y^2 + a^2` and `2*y ≥ 0`, dividing by the larger denominator gives a smaller value.
              exact div_le_div_of_nonneg_left (by nlinarith [hy_nonneg]) hy2_pos hden_ge
        _ = (2 : ℝ) * y⁻¹ := by
              -- `2*y / y^2 = 2 / y`.
              field_simp [hy_pos.ne']

    have h_tendsto : Tendsto (fun y : ℝ => (2 : ℝ) * y⁻¹) atTop (𝓝 (0 : ℝ)) := by
      -- `y⁻¹ → 0`, hence `2*y⁻¹ → 0`.
      simpa [mul_assoc] using (tendsto_const_nhds.mul (tendsto_inv_atTop_zero : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 (0 : ℝ))))
    -- Apply the squeeze lemma.
    exact squeeze_zero_norm' h_le h_tendsto

  /-
  Step 5: Define the absolutely integrable function that remains after integration by parts.
  -/
  let g : ℝ → ℝ := fun x => Real.cos x * (a ^ 2 - x ^ 2) / (x ^ 2 + a ^ 2) ^ 2

  /-
  Step 6: Prove `g` is integrable on `ℝ`.

  We use the domination

  `|g x| ≤ (x^2 + a^2)⁻¹`,

  coming from `|a^2 - x^2| ≤ a^2 + x^2` and `|cos x| ≤ 1`.
  -/
  have hg_int : Integrable g := by
    -- Start from integrability of `(x^2+a^2)⁻¹`.
    have hInv : Integrable (fun x : ℝ => (x ^ 2 + a ^ 2)⁻¹) := integrable_inv_sq_add_sq a ha
    -- Measurability of `g` (it is continuous).
    have hg_meas : AEStronglyMeasurable g := by
      fun_prop
    -- Pointwise bound.
    have hBound : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), ‖g x‖ ≤ (x ^ 2 + a ^ 2)⁻¹ := by
      refine MeasureTheory.ae_of_all _ (fun x => ?_)
      -- Convert norm to abs.
      simp [g, Real.norm_eq_abs]
      -- Use `|cos x| ≤ 1`.
      have hcos : |Real.cos x| ≤ (1 : ℝ) := abs_cos_le_one x
      -- Use `|a^2 - x^2| ≤ a^2 + x^2`.
      have habs : |a ^ 2 - x ^ 2| ≤ a ^ 2 + x ^ 2 := by
        -- This is the standard inequality `|u+v| ≤ |u| + |v|` applied to `u = a^2`, `v = -x^2`.
        -- We then simplify using `|a^2| = a^2` and `|-x^2| = x^2`.
        have h := abs_add_le (a ^ 2) (-x ^ 2)
        -- Rewrite `a^2 - x^2` as `a^2 + (-x^2)` and simplify the absolute values.
        simpa [sub_eq_add_neg, abs_of_nonneg (sq_nonneg a), abs_neg,
          abs_of_nonneg (sq_nonneg x), add_comm, add_left_comm, add_assoc] using h
      -- Denominator positivity.
      have hden_pos : 0 < (x ^ 2 + a ^ 2) ^ 2 := by
        have hpos : 0 < x ^ 2 + a ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_pos ha)
        simpa [pow_two] using mul_pos hpos hpos
      -- Now bound:
      -- `|cos|*|a^2-x^2|/(x^2+a^2)^2 ≤ 1*(a^2+x^2)/(x^2+a^2)^2 = 1/(x^2+a^2)`.
      calc
        |Real.cos x| * |a ^ 2 - x ^ 2| / (x ^ 2 + a ^ 2) ^ 2
            ≤ (1 : ℝ) * (a ^ 2 + x ^ 2) / (x ^ 2 + a ^ 2) ^ 2 := by
                -- First we show the numerator is bounded.
                have hnum : |Real.cos x| * |a ^ 2 - x ^ 2| ≤ 1 * (a ^ 2 + x ^ 2) := by
                  calc
                    |Real.cos x| * |a ^ 2 - x ^ 2| ≤ 1 * |a ^ 2 - x ^ 2| := by gcongr
                    _ ≤ 1 * (a ^ 2 + x ^ 2) := by gcongr
                -- Now divide by the nonnegative denominator.
                have hpos_den' : 0 ≤ (x ^ 2 + a ^ 2) ^ 2 := le_of_lt hden_pos
                exact div_le_div_of_nonneg_right hnum hpos_den'
        _ = (x ^ 2 + a ^ 2)⁻¹ := by
              -- `1*(a^2+x^2)/(x^2+a^2)^2 = 1/(x^2+a^2)`.
              -- Use commutativity to match `a^2 + x^2` with `x^2 + a^2`.
              have hswap : (a ^ 2 + x ^ 2) = (x ^ 2 + a ^ 2) := by ring
              have hne : x ^ 2 + a ^ 2 ≠ 0 := by
                have : 0 < x ^ 2 + a ^ 2 :=
                  add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_pos ha)
                exact ne_of_gt this
              -- After rewriting, the goal is a one-line `field_simp`.
              -- (We keep the steps explicit to avoid brittle simp behavior.)
              rw [hswap]
              field_simp [pow_two, hne]
    exact Integrable.mono' hInv (by
      -- measurability
      exact hg_meas) hBound

  /-
  Step 7: Use `intervalIntegral_tendsto_integral` to get

  `∫_{-y}^{y} g → ∫_{ℝ} g`.
  -/
  have hTendsto_g : Tendsto (fun y : ℝ => ∫ x in -y..y, g x) atTop (𝓝 (∫ x : ℝ, g x)) := by
    have ha' : Tendsto (fun y : ℝ => -y) atTop atBot := by
      simpa using (tendsto_neg_atTop_atBot)
    have hb' : Tendsto (fun y : ℝ => y) atTop atTop := tendsto_id
    simpa using (MeasureTheory.intervalIntegral_tendsto_integral (μ := (volume : Measure ℝ))
      (f := g) (a := fun y : ℝ => -y) (b := fun y : ℝ => y) hg_int ha' hb')

  /-
  Step 8: Evaluate the whole-line integral `∫ g`.

  We rewrite `g` as a linear combination of

  - `cos x / (x^2+a^2)` and
  - `cos x / (x^2+a^2)^2`,

  then use the lemmas from Parts A and B.
  -/
  have hEval_g : (∫ x : ℝ, g x) = Real.pi * Real.exp (-a) := by
    -- Step 8.1: introduce the two known integrals.
    have hK1 : (∫ x : ℝ, Real.cos x / (x ^ 2 + a ^ 2)) = Real.pi * (Real.exp (-a) / a) :=
      integral_cos_div_sq_add_sq a ha
    have hK2 : (∫ x : ℝ, Real.cos x / (x ^ 2 + a ^ 2) ^ 2)
        = Real.pi * Real.exp (-a) * ((a + 1) / (2 * a ^ 3)) :=
      integral_cos_div_sq_add_sq_sq a ha

    -- Step 8.2: rewrite `g` pointwise.
    have hPoint : g = fun x : ℝ => (2 * a ^ 2) * (Real.cos x / (x ^ 2 + a ^ 2) ^ 2)
        - (Real.cos x / (x ^ 2 + a ^ 2)) := by
      funext x
      -- Pure algebraic rewriting.
      -- We use the identity:
      -- `(a^2 - x^2)/(x^2+a^2)^2 = 2a^2/(x^2+a^2)^2 - 1/(x^2+a^2)`.
      -- First unfold `g` so the goal becomes a rational-identity.
      simp [g]
      field_simp [ha0]
      ring

    -- Step 8.3: prove integrability of the two pieces so we can use `integral_sub`.
    have hI1 : Integrable (fun x : ℝ => (2 * a ^ 2) * (Real.cos x / (x ^ 2 + a ^ 2) ^ 2)) := by
      -- constant multiple of an integrable function
      have hbase : Integrable (fun x : ℝ => Real.cos x / (x ^ 2 + a ^ 2) ^ 2) :=
        integrable_cos_div_sq_add_sq_sq a ha
      -- Multiply first by `a^2`, then by `2`, to avoid associativity-mismatch issues.
      have h1 : Integrable (fun x : ℝ => (a ^ 2) * (Real.cos x / (x ^ 2 + a ^ 2) ^ 2)) :=
        hbase.const_mul (c := (a ^ 2))
      have h2 : Integrable (fun x : ℝ => (2 : ℝ) * ((a ^ 2) * (Real.cos x / (x ^ 2 + a ^ 2) ^ 2))) :=
        h1.const_mul (c := (2 : ℝ))
      -- Finally rewrite `2 * (a^2 * f)` as `(2 * a^2) * f`.
      simpa [mul_assoc] using h2
    have hI2 : Integrable (fun x : ℝ => Real.cos x / (x ^ 2 + a ^ 2)) :=
      integrable_cos_div_sq_add_sq a ha

    -- Step 8.4: compute the integral using linearity.
    calc
      (∫ x : ℝ, g x)
          = ∫ x : ℝ, ((2 * a ^ 2) * (Real.cos x / (x ^ 2 + a ^ 2) ^ 2) - (Real.cos x / (x ^ 2 + a ^ 2))) := by
                simp [hPoint]
      _ = (∫ x : ℝ, (2 * a ^ 2) * (Real.cos x / (x ^ 2 + a ^ 2) ^ 2)) - (∫ x : ℝ, Real.cos x / (x ^ 2 + a ^ 2)) := by
                simp [integral_sub hI1 hI2]
      _ = (2 * a ^ 2) * (∫ x : ℝ, Real.cos x / (x ^ 2 + a ^ 2) ^ 2)
            - (∫ x : ℝ, Real.cos x / (x ^ 2 + a ^ 2)) := by
                -- pull out the constant
                simp [integral_const_mul, mul_assoc]
      _ = (2 * a ^ 2) * (Real.pi * Real.exp (-a) * ((a + 1) / (2 * a ^ 3)))
            - (Real.pi * (Real.exp (-a) / a)) := by
                simp [hK1, hK2]
      _ = Real.pi * Real.exp (-a) := by
                -- final arithmetic simplification
                field_simp [ha0]
                ring

  /-
  Step 9: Combine everything.

  From Step 3 (integration by parts):
  `I(y) = boundary(y) + J(y)`.
  Step 4: `boundary(y) → 0`.
  Step 7: `J(y) → ∫ g`.
  Step 8: `∫ g = π * exp(-a)`.

  Therefore `I(y) → π * exp(-a)`.
  -/
  have hMain : Tendsto (fun y : ℝ => (∫ x in -y..y, x * Real.sin x / (x ^ 2 + a ^ 2))) atTop
      (𝓝 (Real.pi * Real.exp (-a))) := by
    -- Rewrite the integral using `hParts`, then use limit of sum.
    have hRewrite : (fun y : ℝ => ∫ x in -y..y, x * Real.sin x / (x ^ 2 + a ^ 2))
        = fun y : ℝ => (-2 * y * Real.cos y) / (y ^ 2 + a ^ 2) + (∫ x in -y..y, g x) := by
      funext y
      simpa [g] using (hParts y)

    -- Use `tendsto_add` with the two convergences.
    have hSum : Tendsto (fun y : ℝ => (-2 * y * Real.cos y) / (y ^ 2 + a ^ 2) + (∫ x in -y..y, g x)) atTop
        (𝓝 (0 + (∫ x : ℝ, g x))) :=
      (hBoundary_tendsto.add hTendsto_g)

    -- Substitute the evaluation of `∫ g`.
    have : Tendsto (fun y : ℝ => (-2 * y * Real.cos y) / (y ^ 2 + a ^ 2) + (∫ x in -y..y, g x)) atTop
        (𝓝 (Real.pi * Real.exp (-a))) := by
      simpa [hEval_g] using hSum

    -- Finish by rewriting using `hRewrite`.
    simpa [hRewrite] using this

  -- The target statement uses `Real.pi * Real.exp (-a)`.
  simpa [mul_assoc] using hMain
