import Mathlib

open Complex Filter Function Metric Finset MeasureTheory intervalIntegral
open scoped BigOperators Topology



/-Informal Statement

Show that $\int_{0}^{\infty} \frac{\sin x}{x} d x=\frac{\pi}{2}$.
-/

/-Informal Proof

We have $\int_0^{\infty} \frac{\sin x}{x} d x=\frac{1}{2 * i} \int_0^{\infty} \frac{e^{i * x}-e^{-i * x}}{x} d x=\frac{1}{2 * i}\left(\int_0^{\infty} \frac{e^{i * x}-1}{x} d x-\int_0^{\infty} \frac{e^{-i * x}-1}{x} d x=\right.$ $\frac{1}{2 * i} \int_{-\infty}^{\infty} \frac{e^{i * x}-1}{x} d x$. Now integrate along the big and small semicircles $C_0$ and $C_1$ shown below. For $C_0$ : we have that $\int_{C_0} \frac{1}{x} d x=\pi * i$ and $\left|\int_{C_0} \frac{e^{i * x}}{x} d x\right| \leq$ $2 *\left|\int_{C_{00}} \frac{e^{i * x}}{x} d x\right|+\left|\int_{C_{01}} \frac{e^{i * x}}{x} d x\right|$ where $C_{00}$ and $C_{01}$ are shown below $\left(C_{01}\right.$ contains the part of $C_0$ that has points with imaginary parts more than $a$ and $C_{00}$ is one of the other 2 components). We have $\left|\int_{C_{00}} \frac{e^{i * x}}{x} d x\right| \leq$ $\sup _{x \in C_{00}}\left(e^{i * x}\right) / R * \int_{C_{00}}|d x| \leq e^{-a} * \pi$ and $\left|\int_{C_{01}} \frac{e^{i * x}}{x} d x\right| \leq\left|\int_{C_{01}} \frac{1}{x} d x\right| \leq$ $\frac{1}{R} * C * a$ for some constant $C$ (the constant $C$ exists because the length of the curve approaches $a$ as $a / R \rightarrow 0)$. Thus, the integral of $e^{i * x} / x$ over $C_0$ is bounded by $A * e^{-a}+B * a / R$ for some constants $A$ and $B$. Pick $R$ large and $a=\sqrt{R}$ and note that the above tends to 0 . About the integral over $C_1$ : We have $e^{i * x}-1=1+O(x)$ for $x \rightarrow 0$ (this is again from $\sin (x) / x \rightarrow 1$ ),
4
so $\left|\int_{C_1} \frac{e^{i * x}-1}{x} d x\right| \leq O(1) *\left|\int_{C_1} d x\right| \rightarrow 0$ as $x \rightarrow 0$. Thus, we only care about the integral over $C_{00}$ which is $-\pi * i$. Using Cauchy's theorem we get that our integral equals $\frac{1}{2 * i}(-(\pi * i))=\pi / 2$.
-/


/-!
## Formalization strategy (Abel / exponential cut-off)

We formalize the classical Dirichlet integral

`lim_{y→∞} ∫ x in 0..y, sin x / x = π/2`.

Instead of the contour-integral argument sketched in the informal proof, we use a standard
real-analysis approach based on an *exponential cut-off*.

`Step 1.` Define
  * `I y   := ∫ x in 0..y, sin x / x`;
  * `Icut R y := ∫ x in 0..y, (sin x / x) * (1 - exp(-R*x))`.

`Step 2.` For each fixed `R > 0`, prove `Icut R y → arctan R` as `y → ∞`.
  This uses:
  * the identity `(1 - exp(-R*x))/x = ∫ t in 0..R, exp(-t*x)` for `x>0`;
  * swapping integrals (Fubini);
  * an explicit primitive for `sin x * exp(-t*x)` via complex exponentials;
  * dominated convergence.

`Step 3.` For `y ≥ 0`, bound the cut-off error: `dist (I y) (Icut R y) ≤ 1/R`.

`Step 4.` Let `R → ∞` using `arctan R → π/2` and `1/R → 0`.
-/

noncomputable section

/-!
### Definitions used in the proof
-/

/-- The partial integral `I(y) = ∫₀ʸ sin x / x dx` (as an interval integral). -/
noncomputable def DirichletI (y : ℝ) : ℝ := ∫ x in (0 : ℝ)..y, Real.sin x / x

/-- The exponentially cut-off partial integral. -/
noncomputable def Icut (R y : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..y, (Real.sin x / x) * (1 - Real.exp (-R * x))

/-- The inner integral appearing after swapping integrals. -/
noncomputable def innerInt (t y : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..y, Real.sin x * Real.exp (-t * x)

/-!
### Step 1: Complex exponential identity

We first express `sin x * exp (-t*x)` as the imaginary part of a complex exponential.
-/

/-
`Step 1.1.` For real `t x`, rewrite the imaginary part
`im (exp ((I - t) * x))` as `exp(-t*x) * sin x`.
-/
lemma exp_I_sub_im (t x : ℝ) :
    (Complex.exp ((Complex.I - t) * x)).im = Real.exp (-t * x) * Real.sin x := by
  -- Step 1.1.1: Expand `(I - t) * x` into a sum so we can use `exp_add`.
  have hx : ((Complex.I : ℂ) - t) * x = (x : ℂ) * Complex.I + (-(t * x) : ℂ) := by
    ring
  -- Step 1.1.2: Split the exponential, then compute the imaginary part of a product.
  calc
    (Complex.exp (((Complex.I : ℂ) - t) * x)).im
        = (Complex.exp ((x : ℂ) * Complex.I + (-(t * x) : ℂ))).im := by
            simp [hx]
    _ = (Complex.exp ((x : ℂ) * Complex.I) * Complex.exp (-(t * x) : ℂ)).im := by
            simp [Complex.exp_add]
    _ = (Complex.exp ((x : ℂ) * Complex.I)).re * (Complex.exp (-(t * x) : ℂ)).im +
          (Complex.exp ((x : ℂ) * Complex.I)).im * (Complex.exp (-(t * x) : ℂ)).re := by
            simp [Complex.mul_im]
    _ = Real.exp (-(t * x)) * Real.sin x := by
          -- Step 1.1.3: Compute the components explicitly.
          have hxI_re : (cexp (I * (x : ℂ))).re = Real.cos x := by
            simpa [mul_comm] using (Complex.exp_ofReal_mul_I_re x)
          have hxI_im : (cexp (I * (x : ℂ))).im = Real.sin x := by
            simpa [mul_comm] using (Complex.exp_ofReal_mul_I_im x)
          have hExp_re : (cexp (-(t * x : ℝ) : ℂ)).re = Real.exp (-(t * x)) := by
            simpa using (Complex.exp_ofReal_re (-(t * x)))
          have hExp_im : (cexp (-(t * x : ℝ) : ℂ)).im = 0 := by
            simpa using (Complex.exp_ofReal_im (-(t * x)))
          have hx_cast : (-(↑t * ↑x) : ℂ) = (-(t * x : ℝ) : ℂ) := by
            norm_cast
          simp [hx_cast, hxI_re, hxI_im, hExp_re, hExp_im, mul_comm]
    _ = Real.exp (-t * x) * Real.sin x := by
          -- Step 1.1.4: Normalize `-(t*x)` to `(-t)*x`.
          have hneg : -t * x = -(t * x) := by ring
          simp [hneg]

/-!
### Step 2: Closed form for the inner integral

We integrate `sin x * exp (-t*x)` by integrating the complex exponential and taking imaginary parts.
-/

/-
`Step 2.1.` Closed form for `∫₀ʸ sin x * exp(-t*x) dx`.
-/
lemma intervalIntegral_sin_mul_exp_neg_mul (t y : ℝ) :
    ∫ x in (0 : ℝ)..y, Real.sin x * Real.exp (-t * x) =
      ((Complex.exp ((Complex.I - t) * y) - 1) / (Complex.I - t)).im := by
  -- Step 2.1.1: Rewrite the integrand as an imaginary part.
  have h_pointwise : ∀ x : ℝ,
      Real.sin x * Real.exp (-t * x) = (Complex.exp ((Complex.I - t) * x)).im := by
    intro x
    simpa [mul_comm, mul_left_comm, mul_assoc] using (exp_I_sub_im t x).symm

  -- Step 2.1.2: Replace the integrand inside the interval integral.
  have h_rewrite : (∫ x in (0 : ℝ)..y, Real.sin x * Real.exp (-t * x)) =
      ∫ x in (0 : ℝ)..y, (Complex.exp ((Complex.I - t) * x)).im := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    have hneg : -t * x = -(t * x) := by ring
    simpa [hneg] using (h_pointwise x)

  -- Step 2.1.3: Commute `im` with the interval integral.
  have h_cont : Continuous (fun x : ℝ => Complex.exp ((Complex.I - t) * x)) := by
    fun_prop
  have h_int : IntervalIntegrable (fun x : ℝ => Complex.exp ((Complex.I - t) * x)) volume 0 y :=
    h_cont.intervalIntegrable 0 y

  -- Step 2.1.4: Evaluate the complex integral using `integral_exp_mul_complex`.
  calc
    ∫ x in (0 : ℝ)..y, Real.sin x * Real.exp (-t * x)
        = ∫ x in (0 : ℝ)..y, (Complex.exp ((Complex.I - t) * x)).im := h_rewrite
    _ = (∫ x in (0 : ℝ)..y, Complex.exp ((Complex.I - t) * x)).im := by
          simpa using (Complex.imCLM.intervalIntegral_comp_comm (a := (0 : ℝ)) (b := y) h_int)
    _ = ((Complex.exp ((Complex.I - t) * y) - 1) / (Complex.I - t)).im := by
          have hne : (Complex.I - (t : ℂ)) ≠ 0 := by
            intro h
            have : ((Complex.I - (t : ℂ))).im = 0 := by simp [h]
            simp at this
          simp [integral_exp_mul_complex (a := (0 : ℝ)) (b := y) hne]

/-!
### Step 3: Evaluate the complex limit value
-/

/-
`Step 3.1.` Compute `im (-(1) / (I - t))` as `1 / (1 + t^2)`.
-/
lemma im_neg_one_div_I_sub (t : ℝ) :
    ((-(1 : ℂ)) / (Complex.I - t)).im = 1 / (1 + t ^ 2) := by
  -- Step 3.1.1: Expand the imaginary part of a quotient.
  have h : ((-(1 : ℂ)) / (Complex.I - t)).im = -(-1 / (t * t + 1)) := by
    simp [Complex.div_im, Complex.normSq, sub_eq_add_neg]
  -- Step 3.1.2: Rewrite `-(-1 / a)` as `a⁻¹`.
  have h' : -(-1 / (t * t + 1)) = (t * t + 1)⁻¹ := by
    simp [div_eq_mul_inv]
  -- Step 3.1.3: Normalize to `1 / (1 + t^2)`.
  calc
    ((-(1 : ℂ)) / (Complex.I - t)).im
        = -(-1 / (t * t + 1)) := h
    _ = (t * t + 1)⁻¹ := h'
    _ = 1 / (1 + t ^ 2) := by
          simp [one_div, pow_two, add_comm]

/-!
### Step 4: Exponential decay
-/

/-
`Step 4.1.` For `t > 0`, we have `exp ((I - t) * y) → 0` as `y → ∞`.
-/
lemma tendsto_exp_I_sub_mul_atTop (t : ℝ) (ht : 0 < t) :
    Tendsto (fun y : ℝ => Complex.exp ((Complex.I - t) * y)) atTop (𝓝 0) := by
  -- Step 4.1.1: Use `Complex.tendsto_exp_nhds_zero_iff`: it suffices to control the real part.
  have h_re : Tendsto (fun y : ℝ => Complex.re ((Complex.I - t) * y)) atTop atBot := by
    have ht' : (-t) < 0 := by linarith
    -- `simp` rewrites `re ((I - t) * y)` to `(-t) * y`.
    simpa using
      (tendsto_const_nhds.neg_mul_atTop ht'
        (tendsto_id : Tendsto (fun y : ℝ => y) atTop atTop))
  have hiff :=
    (Complex.tendsto_exp_nhds_zero_iff (f := fun y : ℝ => (Complex.I - t) * y) (l := atTop))
  exact hiff.2 h_re

/-!
### Step 5: Limit of the inner integral
-/

/-
`Step 5.1.` For `t > 0`, the inner integral `inner t y` tends to `1/(1+t^2)` as `y → ∞`.
-/
lemma tendsto_inner_atTop (t : ℝ) (ht : 0 < t) :
    Tendsto (fun y : ℝ => innerInt t y) atTop (𝓝 (1 / (1 + t ^ 2))) := by
  -- Step 5.1.1: Unfold `innerInt`.
  dsimp [innerInt]
  -- Step 5.1.2: Reuse the computation from Step 2 and the limit computation.
  -- (This lemma is essentially Step 5 from the roadmap.)
  --
  -- We repeat the final argument explicitly:
  -- rewrite the integral by Step 2, show the complex exponential tends to 0, and evaluate the limit.
  have h_form : ∀ y : ℝ,
      (∫ x in (0 : ℝ)..y, Real.sin x * Real.exp (-t * x))
        = ((Complex.exp ((Complex.I - t) * y) - 1) / (Complex.I - t)).im := by
    intro y
    simpa using intervalIntegral_sin_mul_exp_neg_mul t y

  have h_exp : Tendsto (fun y : ℝ => Complex.exp ((Complex.I - t) * y)) atTop (𝓝 0) :=
    tendsto_exp_I_sub_mul_atTop t ht

  have h_complex :
      Tendsto (fun y : ℝ => (Complex.exp ((Complex.I - t) * y) - 1) / (Complex.I - t)) atTop
        (𝓝 ((-(1 : ℂ)) / (Complex.I - t))) := by
    have : Tendsto (fun y : ℝ => Complex.exp ((Complex.I - t) * y) - 1) atTop (𝓝 (0 - 1)) :=
      h_exp.sub tendsto_const_nhds
    simpa using this.div_const (Complex.I - t)

  have h_im :
      Tendsto (fun y : ℝ => ((Complex.exp ((Complex.I - t) * y) - 1) / (Complex.I - t)).im) atTop
        (𝓝 (((-(1 : ℂ)) / (Complex.I - t)).im)) :=
    (Complex.imCLM.continuous.tendsto _).comp h_complex

  have h_im' :
      Tendsto (fun y : ℝ => ((Complex.exp ((Complex.I - t) * y) - 1) / (Complex.I - t)).im) atTop
        (𝓝 (1 / (1 + t ^ 2))) := by
    simpa [im_neg_one_div_I_sub t] using h_im

  -- Transport back to the original integral.
  refine h_im'.congr' ?_
  -- Step 5.1.3: The only remaining work is to rewrite the *function* we are taking the limit of.
  --
  -- Concretely:
  --   * our current function is `y ↦ ((exp((I-t)*y)-1)/(I-t)).im`,
  --   * but `innerInt t y` is definitionally `∫ x in 0..y, sin x * exp(-t*x)`.
  --
  -- The lemma `h_form` gives the equality in the direction
  --   `∫ ... = ...im`,
  -- while `Tendsto.congr'` needs `...im = ∫ ...`, so we use `.symm`.
  exact (Eventually.of_forall fun y => by
    simpa using (h_form y).symm)

/-!
### Step 6: Elementary integral identity for `exp (-t*x)`

We compute `∫₀ᴿ exp (-t*x) dt = (1 - exp(-R*x))/x` for `x ≠ 0`.
-/

/-
`Step 6.1.` For `x ≠ 0`, compute `∫ t in 0..R, exp (-t*x)`.
-/
lemma intervalIntegral_exp_neg_mul (x R : ℝ) (hx : x ≠ 0) :
    ∫ t in (0 : ℝ)..R, Real.exp (-t * x) = (1 - Real.exp (-R * x)) / x := by
  -- Step 6.1.1: Rewrite `exp (-t*x)` as `exp ((-x)*t)`.
  have hx' : (-x) ≠ 0 := by simpa using neg_ne_zero.mpr hx
  calc
    ∫ t in (0 : ℝ)..R, Real.exp (-t * x)
        = ∫ t in (0 : ℝ)..R, Real.exp ((-x) * t) := by
            refine intervalIntegral.integral_congr ?_
            intro t ht
            have : -t * x = (-x) * t := by ring
            simp [this]
    _ = (-x)⁻¹ • ∫ u in (-x) * (0 : ℝ)..(-x) * R, Real.exp u := by
          -- Step 6.1.2: Change variables `u = (-x) * t`.
          simpa using
            (intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := R)
              (f := fun u : ℝ => Real.exp u) hx')
    _ = (-x)⁻¹ • (Real.exp ((-x) * R) - Real.exp ((-x) * (0 : ℝ))) := by
          -- Step 6.1.3: Use the primitive of `exp`.
          simp
    _ = (1 - Real.exp (-R * x)) / x := by
          -- Step 6.1.4: Simplify algebra (clear denominators using `hx`).
          have hmul : (-x) * R = -(R * x) := by ring
          field_simp [hx]
          simp [hx, smul_eq_mul]

/-!
### Step 7: Integrability for swapping the double integral
-/

/-
`Step 7.1.` The function `(x,t) ↦ sin x * exp (-t*x)` is integrable on `(0,y] × (0,R]`.

This is the integrability hypothesis required by `intervalIntegral_integral_swap`.
-/
lemma integrable_uncurry_sin_exp_neg_mul (R y : ℝ) (hR : 0 < R) (hy : 0 ≤ y) :
    Integrable (Function.uncurry (fun (x t : ℝ) => Real.sin x * Real.exp (-t * x)))
      ((volume.restrict (Set.uIoc (0 : ℝ) y)).prod (volume.restrict (Set.uIoc (0 : ℝ) R))) := by
  -- Step 7.1.1: Rewrite `uIoc` as `Ioc` (both coordinates are positive in our application).
  simp [Set.uIoc_of_le hy, Set.uIoc_of_le hR.le]

  -- Step 7.1.2: Use `Integrable.mono'` with bound `1`.
  have h_one : Integrable (fun _ : ℝ × ℝ => (1 : ℝ))
      ((volume.restrict (Set.Ioc (0 : ℝ) y)).prod (volume.restrict (Set.Ioc (0 : ℝ) R))) := by
    simp [integrable_const (1 : ℝ)
        (μ := (volume.restrict (Set.Ioc (0 : ℝ) y)).prod (volume.restrict (Set.Ioc (0 : ℝ) R)))]

  refine Integrable.mono' (g := fun _ : ℝ × ℝ => (1 : ℝ)) h_one (by fun_prop) ?_

  -- Step 7.1.3: Prove the bound `‖sin x * exp(-t*x)‖ ≤ 1` almost everywhere.
  have hμ :
      ((volume.restrict (Set.Ioc (0 : ℝ) y)).prod (volume.restrict (Set.Ioc (0 : ℝ) R)))
        = (volume.prod volume).restrict (Set.Ioc (0 : ℝ) y ×ˢ Set.Ioc (0 : ℝ) R) := by
    simpa using
      (Measure.prod_restrict (μ := volume) (ν := volume)
        (s := Set.Ioc (0 : ℝ) y) (t := Set.Ioc (0 : ℝ) R))

  have hmem :
      ∀ᵐ p : ℝ × ℝ ∂((volume.prod volume).restrict (Set.Ioc (0 : ℝ) y ×ˢ Set.Ioc (0 : ℝ) R)),
        p ∈ (Set.Ioc (0 : ℝ) y ×ˢ Set.Ioc (0 : ℝ) R) := by
    simpa using
      (ae_restrict_mem
        (μ := volume.prod volume)
        (s := Set.Ioc (0 : ℝ) y ×ˢ Set.Ioc (0 : ℝ) R)
        ((measurableSet_Ioc : MeasurableSet (Set.Ioc (0 : ℝ) y)).prod
          (measurableSet_Ioc : MeasurableSet (Set.Ioc (0 : ℝ) R))))

  simpa [hμ] using hmem.mono (fun p hp => by
    -- Extract positivity.
    have hx : p.1 ∈ Set.Ioc (0 : ℝ) y := hp.1
    have ht : p.2 ∈ Set.Ioc (0 : ℝ) R := hp.2
    have hx_pos : 0 < p.1 := hx.1
    have ht_pos : 0 < p.2 := ht.1

    -- `exp(-t*x) ≤ 1` since `-t*x ≤ 0`.
    have h_nonneg : 0 ≤ p.2 * p.1 := mul_nonneg ht_pos.le hx_pos.le
    have hrewrite : (-p.2 * p.1) = -(p.2 * p.1) := by ring
    have h_nonpos : (-p.2 * p.1) ≤ 0 := by
      simpa [hrewrite] using (neg_nonpos.mpr h_nonneg)
    have h_exp_le : Real.exp (-p.2 * p.1) ≤ 1 := (Real.exp_le_one_iff).2 h_nonpos

    -- Now bound the absolute value (and hence the norm).
    have h_abs : |Real.sin p.1 * Real.exp (-p.2 * p.1)| ≤ (1 : ℝ) := by
      calc
        |Real.sin p.1 * Real.exp (-p.2 * p.1)|
            = |Real.sin p.1| * Real.exp (-p.2 * p.1) := by
                simp [abs_mul, Real.abs_exp]
        _ ≤ 1 * Real.exp (-p.2 * p.1) := by
                have hsin : |Real.sin p.1| ≤ 1 := Real.abs_sin_le_one p.1
                exact mul_le_mul_of_nonneg_right hsin (by positivity)
        _ ≤ 1 * 1 := by
                exact mul_le_mul_of_nonneg_left h_exp_le (by positivity)
        _ = (1 : ℝ) := by ring

    simpa [Function.uncurry, Real.norm_eq_abs] using h_abs)

/-!
### Step 8: Rewrite the cut-off integral as a double integral
-/

/-
`Step 8.1.` For `R > 0` and `y ≥ 0`, rewrite the cut-off integral `Icut R y` as a double integral.
-/
lemma Icut_eq_double_integral (R y : ℝ) (hR : 0 < R) (hy : 0 ≤ y) :
    Icut R y = ∫ t in (0 : ℝ)..R, innerInt t y := by
  -- Step 8.1.1: Prove the pointwise identity on the `x`-interval.
  have h_pointwise : ∀ x : ℝ, x ∈ Set.uIoc (0 : ℝ) y →
      (Real.sin x / x) * (1 - Real.exp (-R * x)) =
        ∫ t, (Real.sin x * Real.exp (-t * x)) ∂(volume.restrict (Set.uIoc (0 : ℝ) R)) := by
    intro x hx
    -- On `y ≥ 0`, `uIoc 0 y = Ioc 0 y`, hence `x > 0` and in particular `x ≠ 0`.
    have hxI : x ∈ Set.Ioc (0 : ℝ) y := by simpa [Set.uIoc_of_le hy] using hx
    have hx0 : x ≠ 0 := ne_of_gt hxI.1

    -- Rewrite the RHS set integral as an interval integral (since `0 ≤ R`).
    have hRle : (0 : ℝ) ≤ R := hR.le
    have h_uIoc : Set.uIoc (0 : ℝ) R = Set.Ioc (0 : ℝ) R := by
      simp [Set.uIoc_of_le hRle]

    calc
      (Real.sin x / x) * (1 - Real.exp (-R * x))
          = Real.sin x * ((1 - Real.exp (-R * x)) / x) := by
              -- Algebraic rearrangement.
              simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = Real.sin x * (∫ t in (0 : ℝ)..R, Real.exp (-t * x)) := by
              -- Substitute the computed `t`-integral on the RHS.
              -- `intervalIntegral_exp_neg_mul` is stated as an equality
              --   `∫₀ᴿ exp(-t*x) dt = (1 - exp(-R*x))/x`.
              -- We need the *reverse* direction, so we rewrite with `←`.
              simpa using congrArg (fun z => Real.sin x * z) (intervalIntegral_exp_neg_mul x R hx0).symm
      _ = ∫ t in (0 : ℝ)..R, Real.sin x * Real.exp (-t * x) := by
              -- Pull the constant factor `sin x` inside.
              symm
              simp
      _ = ∫ t in Set.Ioc (0 : ℝ) R, Real.sin x * Real.exp (-t * x) := by
              -- Interval integral = set integral on `Ioc` when `0 ≤ R`.
              simpa using
                (intervalIntegral.integral_of_le (a := (0 : ℝ)) (b := R)
                  (μ := (volume : Measure ℝ)) (f := fun t => Real.sin x * Real.exp (-t * x)) hRle)
      _ = ∫ t, (Real.sin x * Real.exp (-t * x)) ∂(volume.restrict (Set.uIoc (0 : ℝ) R)) := by
              -- Rewrite `Ioc` to `uIoc`.
              simp [h_uIoc]

  -- Step 8.1.2: Replace the integrand in `Icut` using `intervalIntegral.integral_congr_ae`.
  have h_ae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc (0 : ℝ) y →
      (Real.sin x / x) * (1 - Real.exp (-R * x)) =
        ∫ t, (Real.sin x * Real.exp (-t * x)) ∂(volume.restrict (Set.uIoc (0 : ℝ) R)) :=
    ae_of_all _ h_pointwise

  have h_replace :
      (∫ x in (0 : ℝ)..y, (Real.sin x / x) * (1 - Real.exp (-R * x)))
        = ∫ x in (0 : ℝ)..y, ∫ t, (Real.sin x * Real.exp (-t * x))
            ∂(volume.restrict (Set.uIoc (0 : ℝ) R)) := by
    simpa using
      (intervalIntegral.integral_congr_ae (a := (0 : ℝ)) (b := y) (μ := (volume : Measure ℝ))
        (f := fun x => (Real.sin x / x) * (1 - Real.exp (-R * x)))
        (g := fun x => ∫ t, (Real.sin x * Real.exp (-t * x)) ∂(volume.restrict (Set.uIoc (0 : ℝ) R)))
        h_ae)

  -- Step 8.1.3: Swap the order of integration.
  have h_swap :
      (∫ x in (0 : ℝ)..y, ∫ t, (Real.sin x * Real.exp (-t * x))
          ∂(volume.restrict (Set.uIoc (0 : ℝ) R)))
        = ∫ t, (∫ x in (0 : ℝ)..y, Real.sin x * Real.exp (-t * x))
            ∂(volume.restrict (Set.uIoc (0 : ℝ) R)) := by
    have h_int :
        Integrable (Function.uncurry (fun (x t : ℝ) => Real.sin x * Real.exp (-t * x)))
          ((volume.restrict (Set.uIoc (0 : ℝ) y)).prod (volume.restrict (Set.uIoc (0 : ℝ) R))) :=
      integrable_uncurry_sin_exp_neg_mul R y hR hy
    simpa using
      (MeasureTheory.intervalIntegral_integral_swap (a := (0 : ℝ)) (b := y)
        (μ := volume.restrict (Set.uIoc (0 : ℝ) R))
        (f := fun x t => Real.sin x * Real.exp (-t * x)) h_int)

  -- Step 8.1.4: Convert the outer set integral back to an interval integral on `0..R`.
  have hRle : (0 : ℝ) ≤ R := hR.le
  have h_uIoc : Set.uIoc (0 : ℝ) R = Set.Ioc (0 : ℝ) R := by
    simp [Set.uIoc_of_le hRle]

  -- Assemble the chain.
  dsimp [Icut, innerInt]
  calc
    (∫ x in (0 : ℝ)..y, (Real.sin x / x) * (1 - Real.exp (-R * x)))
        = ∫ x in (0 : ℝ)..y, ∫ t, (Real.sin x * Real.exp (-t * x))
            ∂(volume.restrict (Set.uIoc (0 : ℝ) R)) := h_replace
    _ = ∫ t, (∫ x in (0 : ℝ)..y, Real.sin x * Real.exp (-t * x))
          ∂(volume.restrict (Set.uIoc (0 : ℝ) R)) := h_swap
    _ = ∫ t in Set.Ioc (0 : ℝ) R, (∫ x in (0 : ℝ)..y, Real.sin x * Real.exp (-t * x)) := by
          -- This is just unfolding the set integral notation and rewriting `uIoc` to `Ioc`.
          simp [h_uIoc]
    _ = ∫ t in (0 : ℝ)..R, (∫ x in (0 : ℝ)..y, Real.sin x * Real.exp (-t * x)) := by
          -- Apply `integral_of_le` backwards.
          symm
          simpa using
            (intervalIntegral.integral_of_le (a := (0 : ℝ)) (b := R)
              (μ := (volume : Measure ℝ))
              (f := fun t => ∫ x in (0 : ℝ)..y, Real.sin x * Real.exp (-t * x)) hRle)

/-!
### Step 9: Measurability and domination for dominated convergence in `t`
-/

/-
`Step 9.1.` The integrand in `t` is a.e. strongly measurable (we use continuity).
-/
lemma aestronglyMeasurable_G (y R : ℝ) :
    AEStronglyMeasurable
      (fun t : ℝ => ((Complex.exp ((Complex.I - t) * y) - 1) / (Complex.I - t)).im)
      (volume.restrict (Set.Ioc (0 : ℝ) R)) := by
  -- Step 9.1.1: Show the denominator is never zero.
  have hne : ∀ t : ℝ, (Complex.I - t) ≠ 0 := by
    intro t h
    have : ((Complex.I - (t : ℂ))).im = 0 := by simp [h]
    simp at this
  -- Step 9.1.2: Build continuity using `Continuous.div`.
  have h_num : Continuous (fun t : ℝ => Complex.exp ((Complex.I - t) * y) - 1) := by
    fun_prop
  have h_den : Continuous (fun t : ℝ => (Complex.I - t)) := by
    fun_prop
  have h_div : Continuous (fun t : ℝ => (Complex.exp ((Complex.I - t) * y) - 1) / (Complex.I - t)) :=
    h_num.div h_den hne
  have h_im : Continuous (fun t : ℝ => ((Complex.exp ((Complex.I - t) * y) - 1) / (Complex.I - t)).im) :=
    (Complex.continuous_im.comp h_div)
  exact h_im.aestronglyMeasurable

/-
`Step 9.2.` A uniform (in `t`) bound on the integrand for `t>0` and `y≥0`.

This is the key domination used in dominated convergence.
-/
lemma abs_G_le_two (t y : ℝ) (ht : 0 < t) (hy : 0 ≤ y) :
    |((Complex.exp ((Complex.I - t) * y) - 1) / (Complex.I - t)).im| ≤ (2 : ℝ) := by
  -- Step 9.2.1: Start from `|im z| ≤ ‖z‖`.
  have him : |((Complex.exp ((Complex.I - t) * y) - 1) / (Complex.I - t)).im|
      ≤ ‖(Complex.exp ((Complex.I - t) * y) - 1) / (Complex.I - t)‖ :=
    Complex.abs_im_le_norm _

  -- Step 9.2.2: Bound `‖exp((I - t)*y)‖ ≤ 1`.
  have h_exp_norm : ‖Complex.exp ((Complex.I - t) * y)‖ ≤ (1 : ℝ) := by
    have ht' : (-t) ≤ 0 := by linarith
    have h_re_nonpos : Complex.re ((Complex.I - t) * y) ≤ 0 := by
      -- `re ((I - t) * y) = (-t) * y ≤ 0`.
      have : (-t) * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ht' hy
      simpa using this
    have : Real.exp (Complex.re ((Complex.I - t) * y)) ≤ Real.exp 0 :=
      Real.exp_le_exp.mpr h_re_nonpos
    simpa [Complex.norm_exp] using this

  -- Step 9.2.3: Bound the numerator `‖exp(...) - 1‖ ≤ 2`.
  have h_num : ‖Complex.exp ((Complex.I - t) * y) - 1‖ ≤ (2 : ℝ) := by
    calc
      ‖Complex.exp ((Complex.I - t) * y) - 1‖
          ≤ ‖Complex.exp ((Complex.I - t) * y)‖ + ‖(1 : ℂ)‖ := by
              simpa using (norm_sub_le (Complex.exp ((Complex.I - t) * y)) (1 : ℂ))
      _ ≤ 1 + 1 := add_le_add h_exp_norm (by simp)
      _ = (2 : ℝ) := by ring

  -- Step 9.2.4: Bound the denominator `1 ≤ ‖I - t‖`.
  have h_den : (1 : ℝ) ≤ ‖Complex.I - t‖ := by
    have : |(Complex.I - t).im| ≤ ‖Complex.I - t‖ := Complex.abs_im_le_norm (Complex.I - t)
    simpa using this

  -- Step 9.2.5: Combine the bounds for the quotient.
  have h_norm : ‖(Complex.exp ((Complex.I - t) * y) - 1) / (Complex.I - t)‖ ≤ (2 : ℝ) := by
    have h_nonneg : 0 ≤ ‖Complex.exp ((Complex.I - t) * y) - 1‖ := by positivity
    calc
      ‖(Complex.exp ((Complex.I - t) * y) - 1) / (Complex.I - t)‖
          = ‖Complex.exp ((Complex.I - t) * y) - 1‖ / ‖Complex.I - t‖ := by
              simp
      _ ≤ ‖Complex.exp ((Complex.I - t) * y) - 1‖ := div_le_self h_nonneg h_den
      _ ≤ (2 : ℝ) := h_num

  exact him.trans h_norm

/-!
### Step 10: Convergence of the cut-off integral
-/

/-
`Step 10.1.` For fixed `R > 0`, `Icut R y → arctan R` as `y → ∞`.
-/
lemma tendsto_Icut_atTop (R : ℝ) (hR : 0 < R) :
    Tendsto (fun y : ℝ => Icut R y) atTop (𝓝 (Real.arctan R)) := by
  -- Step 10.1.1: Replace `Icut R y` by the double integral (valid for `y ≥ 0`).
  have hy_event : ∀ᶠ y in atTop, (0 : ℝ) ≤ y := Filter.eventually_ge_atTop 0

  -- Define the `t`-integrand we will use for dominated convergence.
  let G : ℝ → ℝ → ℝ :=
    fun y t => ((Complex.exp ((Complex.I - t) * y) - 1) / (Complex.I - t)).im

  -- Step 10.1.2: Show that the double integral equals `∫ t in 0..R, G y t`.
  have h_double_eq : ∀ y : ℝ, (0 : ℝ) ≤ y →
      (∫ t in (0 : ℝ)..R, innerInt t y) = ∫ t in (0 : ℝ)..R, G y t := by
    intro y hy
    -- The equality `inner t y = G y t` holds for all `t` (Step 2).
    refine intervalIntegral.integral_congr ?_
    intro t ht
    -- `simp` uses the closed form from Step 2.
    simpa [G, innerInt] using (intervalIntegral_sin_mul_exp_neg_mul t y)

  -- Step 10.1.3: Prove `∫ t in 0..R, G y t → ∫ t in 0..R, 1/(1+t^2)` by dominated convergence.
  have hRle : (0 : ℝ) ≤ R := hR.le
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) R)

  have h_dom : Tendsto (fun y : ℝ => ∫ t, G y t ∂μ) atTop (𝓝 (∫ t, (1 / (1 + t ^ 2)) ∂μ)) := by
    -- Apply the filter-version dominated convergence theorem.
    -- We use the constant bound `2`.
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (l := atTop)
      (bound := fun _ : ℝ => (2 : ℝ))
      (F := fun y t => G y t)
      (f := fun t => (1 / (1 + t ^ 2)))
      ?_ ?_ ?_ ?_
    · -- Measurability: `G y` is continuous hence a.e. strongly measurable.
      refine (Eventually.of_forall fun y => ?_)
      -- `aestronglyMeasurable_G` is exactly this statement.
      simpa [G, μ] using (aestronglyMeasurable_G y R)
    · -- Domination: for `y ≥ 0`, we have `|G y t| ≤ 2` a.e. on `(0,R]`.
      refine hy_event.mono ?_
      intro y hy
      -- We need: `∀ᵐ t ∂μ, ‖G y t‖ ≤ 2`.
      have hmem : ∀ᵐ t ∂μ, t ∈ Set.Ioc (0 : ℝ) R := by
        -- Step 10.1.3.1: Points are a.e. in the restricting set.
        --
        -- We spell out all implicit arguments so that typeclass inference does *not* get stuck
        -- on metavariables like `OrderClosedTopology ?m`.
        simpa [μ] using
          (ae_restrict_mem (μ := (volume : Measure ℝ)) (s := Set.Ioc (0 : ℝ) R) measurableSet_Ioc)
      refine hmem.mono ?_
      intro t ht
      -- Use the bound from Step 9.2.
      have : |G y t| ≤ (2 : ℝ) := abs_G_le_two t y ht.1 hy
      simpa [Real.norm_eq_abs] using this
    · -- Integrability of the bound function `2` on a finite interval.
      -- (The measure `μ` is finite because it is `volume.restrict (Ioc 0 R)`.)
      simp [μ, integrable_const (2 : ℝ) (μ := μ)]
    · -- Pointwise convergence a.e.: `G y t → 1/(1+t^2)` for each `t ∈ (0,R]`.
      have hmem : ∀ᵐ t ∂μ, t ∈ Set.Ioc (0 : ℝ) R := by
        -- Step 10.1.3.2: Same a.e. membership fact as above.
        simpa [μ] using
          (ae_restrict_mem (μ := (volume : Measure ℝ)) (s := Set.Ioc (0 : ℝ) R) measurableSet_Ioc)
      refine hmem.mono ?_
      intro t ht
      -- For `t>0`, the inner integral converges to `1/(1+t^2)`.
      -- We use `tendsto_inner_atTop` and the equality `inner = G`.
      have h_inner : Tendsto (fun y : ℝ => innerInt t y) atTop (𝓝 (1 / (1 + t ^ 2))) :=
        tendsto_inner_atTop t ht.1
      -- Replace `inner` by `G` using the closed form.
      refine h_inner.congr' ?_
      exact (Eventually.of_forall fun y => by
        simpa [G, innerInt] using (intervalIntegral_sin_mul_exp_neg_mul t y))

  -- Step 10.1.4: Convert back from the restricted-measure integral to the interval integral.
  have h_dom_interval :
      Tendsto (fun y : ℝ => ∫ t in (0 : ℝ)..R, G y t) atTop (𝓝 (∫ t in (0 : ℝ)..R, 1 / (1 + t ^ 2))) := by
    -- Step 10.1.4.1: First convert the *limit value* from a restricted-measure integral
    -- to an interval integral.
    have h_limEq : (∫ t, (1 / (1 + t ^ 2)) ∂μ) = ∫ t in (0 : ℝ)..R, 1 / (1 + t ^ 2) := by
      -- Step 10.1.4.1.1: Expand `μ` into a set integral.
      -- Step 10.1.4.1.2: Use `intervalIntegral.integral_of_le` (symmetry) to go back.
      calc
        (∫ t, (1 / (1 + t ^ 2)) ∂μ)
            = ∫ t in Set.Ioc (0 : ℝ) R, (1 / (1 + t ^ 2)) ∂volume := by
                simp [μ]
        _ = ∫ t in (0 : ℝ)..R, (1 / (1 + t ^ 2)) := by
              exact
                (intervalIntegral.integral_of_le (a := (0 : ℝ)) (b := R)
                  (μ := (volume : Measure ℝ)) (f := fun t => (1 / (1 + t ^ 2))) hRle).symm

    -- Step 10.1.4.2: Next convert the *functions* `y ↦ ∫ G y` from a restricted-measure integral
    -- to an interval integral.
    have h_funEq : ∀ y : ℝ, (∫ t, G y t ∂μ) = ∫ t in (0 : ℝ)..R, G y t := by
      intro y
      calc
        (∫ t, G y t ∂μ) = ∫ t in Set.Ioc (0 : ℝ) R, (G y t) ∂volume := by
          simp [μ]
        _ = ∫ t in (0 : ℝ)..R, (G y t) := by
          exact
            (intervalIntegral.integral_of_le (a := (0 : ℝ)) (b := R)
              (μ := (volume : Measure ℝ)) (f := fun t => (G y t)) hRle).symm

    -- Step 10.1.4.3: Rewrite the limit point using `h_limEq` and then apply `h_dom`.
    have h_dom' : Tendsto (fun y : ℝ => ∫ t, G y t ∂μ) atTop (𝓝 (∫ t in (0 : ℝ)..R, 1 / (1 + t ^ 2))) := by
      -- `rw` changes the limit point without running any simplification that could accidentally
      -- evaluate the interval integral.
      rw [← h_limEq]
      exact h_dom

    -- Step 10.1.4.4: Finally, transport the limit along the (pointwise) equality `h_funEq`.
    refine h_dom'.congr' ?_
    exact (Eventually.of_forall fun y => h_funEq y)

  -- Step 10.1.5: Evaluate `∫₀ᴿ 1/(1+t^2) dt = arctan R`.
  have h_eval : (∫ t in (0 : ℝ)..R, 1 / (1 + t ^ 2)) = Real.arctan R := by
    -- This is `integral_inv_one_add_sq` with `a = 0`, plus `arctan 0 = 0`.
    simp [one_div]

  -- Step 10.1.6: Combine everything.
  -- First: show `Icut R y` is eventually equal to the interval integral of `inner`.
  have h_eventually : ∀ᶠ y in atTop, Icut R y = ∫ t in (0 : ℝ)..R, innerInt t y := by
    refine hy_event.mono ?_
    intro y hy
    simpa using (Icut_eq_double_integral R y hR hy)

  -- Now transport the limit along the eventual equality and the other equalities.
  have h_target : Tendsto (fun y : ℝ => ∫ t in (0 : ℝ)..R, innerInt t y) atTop (𝓝 (Real.arctan R)) := by
    -- Replace `inner` by `G` inside the integral.
    have h1 : Tendsto (fun y : ℝ => ∫ t in (0 : ℝ)..R, innerInt t y) atTop
        (𝓝 (∫ t in (0 : ℝ)..R, 1 / (1 + t ^ 2))) := by
      -- Use `h_dom_interval` plus the pointwise equality from `h_double_eq`.
      have h_eq : ∀ y : ℝ, (0 : ℝ) ≤ y →
          (∫ t in (0 : ℝ)..R, innerInt t y) = ∫ t in (0 : ℝ)..R, G y t := h_double_eq
      -- On `atTop`, `y ≥ 0` eventually.
      refine (h_dom_interval.congr' ?_)
      refine hy_event.mono ?_
      intro y hy
      -- Step 10.1.6.1: We need the equality in the direction
      --   `∫ G = ∫ innerInt`,
      -- but `h_eq` gives `∫ innerInt = ∫ G`, so we take `.symm`.
      exact (h_eq y hy).symm
    -- Evaluate the limiting integral.
    simpa [h_eval] using h1

  -- Final: apply eventual equality.
  -- Step 10.1.7: Convert the `∀ᶠ` equality into an `EventuallyEq` and use it to replace
  -- `∫ t in 0..R, innerInt t y` by `Icut R y`.
  have h_eventually_eq :
      (fun y : ℝ => Icut R y) =ᶠ[atTop] (fun y : ℝ => ∫ t in (0 : ℝ)..R, innerInt t y) :=
    h_eventually
  -- We need the symmetry direction because `h_target` is a limit statement about the integral.
  exact h_target.congr' h_eventually_eq.symm

/-!
### Step 11: Error bound between `I` and `Icut`
-/

/-
`Step 11.1.` On `(0, y]`, we have `|sin x / x| ≤ 1`.
-/
lemma abs_sin_div_le_one_of_pos {x : ℝ} (hx : 0 < x) : |Real.sin x / x| ≤ 1 := by
  -- Step 11.1.1: Rewrite `|sin x / x|`.
  rw [abs_div, abs_of_pos hx]
  -- Step 11.1.2: Use `div_le_one` (valid since `x > 0`).
  refine (div_le_one hx).2 ?_
  -- Step 11.1.3: `|sin x| ≤ |x| = x`.
  -- Note: `Real.abs_sin_le_abs` has an *implicit* variable `{x : ℝ}` in mathlib,
  -- so we must pass it via the named argument `(x := x)`.
  simpa [abs_of_pos hx] using (Real.abs_sin_le_abs (x := x))

/-
`Step 11.2.` For `R > 0` and `y ≥ 0`, the cut-off error satisfies `dist (I y) (Icut R y) ≤ 1/R`.
-/
lemma dist_I_Icut_le (R y : ℝ) (hR : 0 < R) (hy : 0 ≤ y) :
    dist (DirichletI y) (Icut R y) ≤ 1 / R := by
  -- Step 11.2.1: Rewrite the distance on `ℝ` as an absolute value.
  simp only [DirichletI, Icut, Real.dist_eq]
  -- Now the goal is `|I y - Icut R y| ≤ 1/R`.

  -- Step 11.2.2: Prove interval integrability of the two integrands on `0..y`.
  have h_f : IntervalIntegrable (fun x : ℝ => Real.sin x / x) volume 0 y := by
    -- Step 11.2.2.1: Define the empty set for the reversed interval.
    have hy' : Set.Ioc y (0 : ℝ) = ∅ := Set.Ioc_eq_empty (by linarith)
    -- Step 11.2.2.2: Split the interval integrability into two parts.
    constructor
    · -- Step 11.2.2.3: Integrability on `Ioc 0 y` using `Integrable.mono'`.
      rw [IntegrableOn]
      apply Integrable.mono' (g := fun _ => (1 : ℝ))
      · exact integrable_const 1
      · have h_cont : ContinuousOn (fun x : ℝ => Real.sin x / x) (Set.Ioc 0 y) := by
          apply ContinuousOn.div Real.continuous_sin.continuousOn continuous_id.continuousOn
          intro x hx; exact ne_of_gt hx.1
        exact h_cont.aestronglyMeasurable measurableSet_Ioc
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        simp only [Real.norm_eq_abs]
        have hx_pos : 0 < x := hx.1
        rw [abs_div, abs_of_pos hx_pos]
        have h1 : |Real.sin x| ≤ |x| := Real.abs_sin_le_abs
        rw [abs_of_pos hx_pos] at h1
        exact (div_le_one hx_pos).mpr h1
    · simp only [hy', integrableOn_empty]

  have h_g :
      IntervalIntegrable (fun x : ℝ => (Real.sin x / x) * (1 - Real.exp (-R * x))) volume 0 y := by
    have hy' : Set.Ioc y (0 : ℝ) = ∅ := Set.Ioc_eq_empty (by linarith)
    constructor
    · rw [IntegrableOn]
      apply Integrable.mono' (g := fun _ => (1 : ℝ))
      · exact integrable_const 1
      · have h_cont : ContinuousOn (fun x : ℝ => (Real.sin x / x) * (1 - Real.exp (-R * x)))
            (Set.Ioc 0 y) := by
          apply ContinuousOn.mul
          · apply ContinuousOn.div Real.continuous_sin.continuousOn continuous_id.continuousOn
            intro x hx; exact ne_of_gt hx.1
          · apply ContinuousOn.sub continuousOn_const
            exact (Real.continuous_exp.comp (by continuity : Continuous (fun x => -R * x))).continuousOn
        exact h_cont.aestronglyMeasurable measurableSet_Ioc
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        simp only [Real.norm_eq_abs]
        have hx_pos : 0 < x := hx.1
        have h1 : |Real.sin x / x| ≤ 1 := by
          rw [abs_div, abs_of_pos hx_pos]
          have h' : |Real.sin x| ≤ |x| := Real.abs_sin_le_abs
          rw [abs_of_pos hx_pos] at h'; exact (div_le_one hx_pos).mpr h'
        have hexp : Real.exp (-R * x) ≤ 1 := by
          have : -R * x ≤ 0 := by nlinarith [hR, hx_pos]
          exact Real.exp_le_one_iff.2 this
        have hdiff : |1 - Real.exp (-R * x)| ≤ 1 := by
          have hnonneg : 0 ≤ 1 - Real.exp (-R * x) := sub_nonneg.mpr hexp
          rw [abs_of_nonneg hnonneg]; linarith [Real.exp_nonneg (-R * x)]
        calc |(Real.sin x / x) * (1 - Real.exp (-R * x))|
            = |Real.sin x / x| * |1 - Real.exp (-R * x)| := abs_mul _ _
          _ ≤ 1 * 1 := mul_le_mul h1 hdiff (by positivity) (by positivity)
          _ = 1 := by ring
    · simp only [hy', integrableOn_empty]

  -- Step 11.2.3: The difference simplifies to an integral of `(sin x / x) * exp(-R*x)`.
  -- Step 11.2.3.1: Integral of the difference equals difference of integrals.
  have h_sub :
      (∫ x in (0 : ℝ)..y, Real.sin x / x) -
        (∫ x in (0 : ℝ)..y, (Real.sin x / x) * (1 - Real.exp (-R * x)))
          = ∫ x in (0 : ℝ)..y,
              (Real.sin x / x) - (Real.sin x / x) * (1 - Real.exp (-R * x)) :=
    (intervalIntegral.integral_sub h_f h_g).symm

  -- Step 11.2.3.2: Algebraically simplify the integrand.
  have h_simpl : ∀ x : ℝ, (Real.sin x / x) - (Real.sin x / x) * (1 - Real.exp (-R * x))
        = (Real.sin x / x) * Real.exp (-R * x) := fun x => by ring

  -- Step 11.2.4: Bound the absolute value.
  -- The strategy: rewrite the difference as an integral of `(sin x / x) * exp(-R*x)`, bound by `∫ exp(-R*x) dx`,
  -- and compute that integral explicitly.

  -- Step 11.2.4.1: Rewrite using h_sub and h_simpl.
  rw [h_sub]
  have h_congr : (∫ x in (0 : ℝ)..y,
        (Real.sin x / x) - (Real.sin x / x) * (1 - Real.exp (-R * x)))
      = ∫ x in (0 : ℝ)..y, (Real.sin x / x) * Real.exp (-R * x) := by
    apply intervalIntegral.integral_congr
    intro x _; exact h_simpl x

  rw [h_congr]

  -- Step 11.2.4.2: Prove integrability of the new integrand.
  have h_int : IntervalIntegrable (fun x => (Real.sin x / x) * Real.exp (-R * x)) volume 0 y := by
    have hy' : Set.Ioc y (0 : ℝ) = ∅ := Set.Ioc_eq_empty (by linarith)
    constructor
    · rw [IntegrableOn]
      apply Integrable.mono' (g := fun _ => (1 : ℝ))
      · exact integrable_const 1
      · have h_cont : ContinuousOn (fun x : ℝ => (Real.sin x / x) * Real.exp (-R * x))
            (Set.Ioc 0 y) := by
          apply ContinuousOn.mul
          · apply ContinuousOn.div Real.continuous_sin.continuousOn continuous_id.continuousOn
            intro x hx; exact ne_of_gt hx.1
          · exact (Real.continuous_exp.comp (by continuity : Continuous (fun x => -R * x))).continuousOn
        exact h_cont.aestronglyMeasurable measurableSet_Ioc
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        simp only [Real.norm_eq_abs]
        have hx_pos : 0 < x := hx.1
        have h1 : |Real.sin x / x| ≤ 1 := by
          rw [abs_div, abs_of_pos hx_pos]
          have h' : |Real.sin x| ≤ |x| := Real.abs_sin_le_abs
          rw [abs_of_pos hx_pos] at h'; exact (div_le_one hx_pos).mpr h'
        calc |(Real.sin x / x) * Real.exp (-R * x)|
            = |Real.sin x / x| * |Real.exp (-R * x)| := abs_mul _ _
          _ = |Real.sin x / x| * Real.exp (-R * x) := by simp [Real.abs_exp]
          _ ≤ 1 * Real.exp (-R * x) := mul_le_mul_of_nonneg_right h1 (by positivity)
          _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left
              (Real.exp_le_one_iff.2 (by nlinarith [hR, hx_pos])) (by positivity)
          _ = 1 := by ring
    · simp only [hy', integrableOn_empty]

  -- Step 11.2.4.3: Prove integrability of exp(-R*x).
  have h_exp_int : IntervalIntegrable (fun x => Real.exp (-R * x)) volume 0 y := by
    exact (Real.continuous_exp.comp (by continuity : Continuous (fun x => -R * x))).intervalIntegrable 0 y

  -- Step 11.2.4.4: Pointwise bound on `Icc 0 y`.
  have h_le : ∀ x ∈ Set.Icc (0 : ℝ) y,
      |(Real.sin x / x) * Real.exp (-R * x)| ≤ Real.exp (-R * x) := by
    intro x hx
    by_cases hx0 : x = 0
    · -- At x = 0: |(sin 0 / 0) * exp(0)| = |0 * 1| = 0 ≤ 1 = exp(0).
      simp only [hx0, Real.sin_zero, zero_div, zero_mul, abs_zero, mul_zero, Real.exp_zero]
      exact zero_le_one
    · -- For x ≠ 0 in [0, y], we have x > 0.
      have hx_pos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
      have h1 : |Real.sin x / x| ≤ 1 := by
        rw [abs_div, abs_of_pos hx_pos]
        have h' : |Real.sin x| ≤ |x| := Real.abs_sin_le_abs
        rw [abs_of_pos hx_pos] at h'; exact (div_le_one hx_pos).mpr h'
      calc |(Real.sin x / x) * Real.exp (-R * x)|
          = |Real.sin x / x| * |Real.exp (-R * x)| := abs_mul _ _
        _ = |Real.sin x / x| * Real.exp (-R * x) := by simp [Real.abs_exp]
        _ ≤ 1 * Real.exp (-R * x) := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = Real.exp (-R * x) := by ring

  -- Step 11.2.4.5: Apply interval integral bound.
  have h_bound : |∫ x in (0 : ℝ)..y, (Real.sin x / x) * Real.exp (-R * x)|
      ≤ ∫ x in (0 : ℝ)..y, Real.exp (-R * x) := by
    have h1 : |∫ x in (0 : ℝ)..y, (Real.sin x / x) * Real.exp (-R * x)|
        ≤ ∫ x in (0 : ℝ)..y, |(Real.sin x / x) * Real.exp (-R * x)| :=
      intervalIntegral.abs_integral_le_integral_abs hy
    have h2 : ∫ x in (0 : ℝ)..y, |(Real.sin x / x) * Real.exp (-R * x)|
        ≤ ∫ x in (0 : ℝ)..y, Real.exp (-R * x) :=
      intervalIntegral.integral_mono_on hy h_int.abs h_exp_int h_le
    exact h1.trans h2

  -- Step 11.2.4.6: Compute the exponential integral.
  have h_exp_val : ∫ x in (0 : ℝ)..y, Real.exp (-R * x) = (1 - Real.exp (-R * y)) / R := by
    have hR0 : R ≠ 0 := ne_of_gt hR
    -- Use intervalIntegral_exp_neg_mul with R and y swapped, then convert.
    have h1 : ∫ t in (0 : ℝ)..y, Real.exp (-t * R) = (1 - Real.exp (-y * R)) / R :=
      intervalIntegral_exp_neg_mul R y hR0
    -- Convert `-t * R` to `-R * t` in the integrand.
    have h2 : ∫ x in (0 : ℝ)..y, Real.exp (-R * x) = ∫ t in (0 : ℝ)..y, Real.exp (-t * R) := by
      apply intervalIntegral.integral_congr
      intro t _
      ring_nf
    -- Convert `-y * R` to `-R * y` in the result.
    rw [h2, h1]
    ring_nf

  -- Step 11.2.4.7: Final bound.
  have h_final : (1 - Real.exp (-R * y)) / R ≤ 1 / R := by
    apply div_le_div_of_nonneg_right _ hR.le
    linarith [Real.exp_nonneg (-R * y)]

  exact h_bound.trans (by rw [h_exp_val]; exact h_final)

/-!
### Step 12: Final theorem
-/

theorem Shakarchi_exercise_2_2 :
    Tendsto (fun y => ∫ x in (0 : ℝ)..y, Real.sin x / x) atTop (𝓝 (Real.pi / 2)) := by
  -- Step 12.1: Restate the target function using the abbreviation `DirichletI`.
  have hI : (fun y : ℝ => ∫ x in (0 : ℝ)..y, Real.sin x / x) = DirichletI := by
    rfl
  -- It suffices to prove `Tendsto DirichletI atTop (𝓝 (π/2))`.
  --
  -- We proceed with the metric ε-definition.
  --
  refine (Metric.tendsto_atTop.mpr fun ε hε => ?_)

  -- Step 12.2: Choose `R` large so that:
  --   (i) `1/R < ε/3`,
  --   (ii) `dist (arctan R) (π/2) < ε/3`.
  have h_inv : Tendsto (fun R : ℝ => (1 / R)) atTop (𝓝 (0 : ℝ)) := by
    simpa [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 (0 : ℝ)))
  have h_arctan : Tendsto Real.arctan atTop (𝓝 (Real.pi / 2)) :=
    tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop

  -- Extract an `R₀` for the `1/R` condition.
  rcases (Metric.tendsto_atTop.mp h_inv) (ε / 3) (by nlinarith [hε]) with ⟨R₀, hR₀⟩
  -- Extract an `R₁` for the arctan condition.
  rcases (Metric.tendsto_atTop.mp h_arctan) (ε / 3) (by nlinarith [hε]) with ⟨R₁, hR₁⟩

  -- Choose `R` large enough for both conditions, and also ensure `R > 0`.
  let R : ℝ := max (max R₀ R₁) 1
  -- Step 12.2.1: Prove `R ≥ 1`, hence `R > 0`.
  have hR_ge_one : (1 : ℝ) ≤ R := le_max_right (max R₀ R₁) 1
  have hR_pos : 0 < R := by
    -- `R ≥ 1 > 0` by construction.
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR_ge_one

  -- Step 12.2.2: Prove `1/R < ε/3`.
  have h_small_inv : 1 / R < ε / 3 := by
    -- Use the eventual property at the chosen `R`.
    -- First show `R₀ ≤ R`: `R₀ ≤ max R₀ R₁ ≤ max (max R₀ R₁) 1 = R`.
    have hR_ge : R₀ ≤ R :=
      le_trans (le_max_left R₀ R₁) (le_max_left (max R₀ R₁) 1)
    -- `hR₀` gives `dist (1/R) 0 < ε/3`, i.e., `|1/R - 0| < ε/3`, i.e., `|1/R| < ε/3`.
    have h1 := hR₀ R hR_ge
    -- Since `R > 0`, we have `|1/R| = 1/R`.
    simp only [Real.dist_eq, sub_zero] at h1
    rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / R)] at h1
    exact h1

  -- Step 12.2.3: Prove `dist (arctan R) (π/2) < ε/3`.
  have h_small_arctan : dist (Real.arctan R) (Real.pi / 2) < ε / 3 := by
    -- First show `R₁ ≤ R`: `R₁ ≤ max R₀ R₁ ≤ max (max R₀ R₁) 1 = R`.
    have hR_ge : R₁ ≤ R :=
      le_trans (le_max_right R₀ R₁) (le_max_left (max R₀ R₁) 1)
    have := hR₁ R hR_ge
    simpa [R] using this

  -- Step 12.3: For this fixed `R > 0`, use Step 10 to get `Icut R y` close to `arctan R`.
  have h_cut : Tendsto (fun y : ℝ => Icut R y) atTop (𝓝 (Real.arctan R)) :=
    tendsto_Icut_atTop R hR_pos
  rcases (Metric.tendsto_atTop.mp h_cut) (ε / 3) (by nlinarith [hε]) with ⟨Y, hY⟩

  -- Step 12.4: Take `N = max Y 0` so that we can use the error bound which needs `y ≥ 0`.
  refine ⟨max Y 0, ?_⟩
  intro y hyN
  have hyY : Y ≤ y := le_trans (le_max_left _ _) hyN
  have hy0 : (0 : ℝ) ≤ y := le_trans (le_max_right _ _) hyN

  -- Step 12.5: Apply the triangle inequality:
  --   dist(I y, π/2) ≤ dist(I y, Icut R y) + dist(Icut R y, arctan R) + dist(arctan R, π/2).
  have h1 : dist (DirichletI y) (Icut R y) ≤ 1 / R := dist_I_Icut_le R y hR_pos hy0
  have h2 : dist (Icut R y) (Real.arctan R) < ε / 3 := hY y hyY
  have h3 : dist (Real.arctan R) (Real.pi / 2) < ε / 3 := h_small_arctan

  -- Combine the three estimates.
  have htri : dist (DirichletI y) (Real.pi / 2) ≤
      dist (DirichletI y) (Icut R y) + dist (Icut R y) (Real.arctan R) +
        dist (Real.arctan R) (Real.pi / 2) := by
    -- Two applications of `dist_triangle`.
    calc
      dist (DirichletI y) (Real.pi / 2)
          ≤ dist (DirichletI y) (Icut R y) + dist (Icut R y) (Real.pi / 2) := dist_triangle _ _ _
      _ ≤ dist (DirichletI y) (Icut R y) +
            (dist (Icut R y) (Real.arctan R) + dist (Real.arctan R) (Real.pi / 2)) := by
            gcongr
            exact dist_triangle _ _ _
      _ = dist (DirichletI y) (Icut R y) + dist (Icut R y) (Real.arctan R) +
            dist (Real.arctan R) (Real.pi / 2) := by
            ring

  -- Step 12.6: Finish by bounding each term by `ε/3`.
  have : dist (DirichletI y) (Real.pi / 2) < ε := by
    have h_sum :
        dist (DirichletI y) (Icut R y) + dist (Icut R y) (Real.arctan R) +
          dist (Real.arctan R) (Real.pi / 2)
          < ε := by
      -- `dist(I y, Icut R y) ≤ 1/R < ε/3`, and the other two are `< ε/3`.
      have h1' : dist (DirichletI y) (Icut R y) < ε / 3 := lt_of_le_of_lt h1 h_small_inv
      -- Now sum the three strict inequalities.
      have : dist (DirichletI y) (Icut R y) + dist (Icut R y) (Real.arctan R) +
          dist (Real.arctan R) (Real.pi / 2)
          < (ε / 3) + (ε / 3) + (ε / 3) := by
        nlinarith [h1', h2, h3]
      -- And `(ε/3)+(ε/3)+(ε/3)=ε`.
      simpa using (this.trans_eq (by ring))
    exact lt_of_le_of_lt htri h_sum

  -- Conclude the ε-proof.
  simpa [hI] using this

end
