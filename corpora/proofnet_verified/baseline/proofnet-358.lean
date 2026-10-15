import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Suppose $f^{\prime}(x), g^{\prime}(x)$ exist, $g^{\prime}(x) \neq 0$, and $f(x)=g(x)=0$. Prove that $\lim _{t \rightarrow x} \frac{f(t)}{g(t)}=\frac{f^{\prime}(x)}{g^{\prime}(x)}.$
-/

/-Informal Proof

Since $f(x)=g(x)=0$, we have
$$
\begin{aligned}
\lim _{t \rightarrow x} \frac{f(t)}{g(t)} &=\lim _{t \rightarrow x} \frac{\frac{f(t)-f(x)}{t-x}}{\frac{g(t)-g(x)}{t-x}} \\
&=\frac{\lim _{t \rightarrow x} \frac{f(t)-f(x)}{t-x}}{\lim _{t \rightarrow x} \frac{g(t)-g(x)}{t-x}} \\
&=\frac{f^{\prime}(x)}{g^{\prime}(x)}
\end{aligned}
$$
-/

theorem Rudin_exercise_5_7
  {f g : ℝ → ℝ} {x : ℝ}
  (hf' : DifferentiableAt ℝ f x)
  (hg' : DifferentiableAt ℝ g x)
  (hg'_ne_0 : deriv g x ≠ 0)
  (f0 : f x = 0) (g0 : g x = 0) :
  Tendsto (λ t => f t / g t) (𝓝 x) (𝓝 (deriv f x / deriv g x)) := by
  sorry

/--
The informal reasoning overlooks that `Tendsto` with respect to `𝓝 x` forces the function's
value at `x` to agree with the claimed limit.  Here the quotient `f x / g x` is defined to be
`0 / 0 = 0`, while the ratio `deriv f x / deriv g x` can easily be nonzero (take
`f(t) = g(t) = t - x` so the derivative ratio is `1`).  Hence the formal statement using `𝓝 x`
is false; one must instead work with the punctured neighborhood `𝓝[≠] x`.
-/
theorem Rudin_exercise_5_7_neg :
    ¬ (∀ {f g : ℝ → ℝ} {x : ℝ},
        DifferentiableAt ℝ f x →
        DifferentiableAt ℝ g x →
        deriv g x ≠ 0 →
        f x = 0 → g x = 0 →
        Tendsto (fun t => f t / g t) (𝓝 x) (𝓝 (deriv f x / deriv g x))) := by
  classical
  -- Step 1: Assume the incorrect universal claim and prepare to derive a contradiction.
  intro h
  -- Step 2: Specialize the claim to the elementary counterexample `f t = g t = t` at `x = 0`.
  let f0 : ℝ → ℝ := fun t => t
  have hf_diff : DifferentiableAt ℝ f0 0 :=
    by simp [f0]
  have hg_diff : DifferentiableAt ℝ f0 0 := hf_diff
  have hg_deriv_ne : deriv f0 0 ≠ 0 := by simp [f0]
  have hf0 : f0 0 = 0 := by simp [f0]
  have hg0 : f0 0 = 0 := hf0
  have hlim := h (f := f0) (g := f0) (x := (0 : ℝ)) hf_diff hg_diff hg_deriv_ne hf0 hg0
  have hlim' : Tendsto (fun t => f0 t / f0 t) (𝓝 0) (𝓝 (1 : ℝ)) := by
    simpa [f0] using hlim
  -- Step 3: Translate the `Tendsto` statement into the fact that `f0 t / f0 t` eventually lies in a ball around 1.
  have h_eventually :=
    hlim'.eventually (Metric.ball_mem_nhds (1 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2))
  have hset : {t : ℝ | f0 t / f0 t ∈ Metric.ball (1 : ℝ) (1 / 2)} ∈ 𝓝 (0 : ℝ) := by
    simpa [Filter.Eventually] using h_eventually
  have hcontains : (0 : ℝ) ∈ {t : ℝ | f0 t / f0 t ∈ Metric.ball (1 : ℝ) (1 / 2)} :=
    mem_of_mem_nhds hset
  -- Step 4: Evaluate the membership statement at `t = 0` to get the impossible inequality `1 < 1/2`.
  have hlt : (1 : ℝ) < 1 / 2 := by
    simpa [f0, Metric.mem_ball] using hcontains
  have hle : (1 / 2 : ℝ) ≤ 1 := by norm_num
  exact (lt_irrefl (1 : ℝ)) (lt_of_lt_of_le hlt hle)

/--
Corrected formal statement: when we take the limit of the quotient along the punctured filter
`𝓝[≠] x` (the usual notion of limit as `t → x`), the quotient converges to
`deriv f x / deriv g x`.  The proof rewrites the quotient in terms of slopes and uses the usual
limit characterization of derivatives.
-/
theorem Rudin_exercise_5_7_corrected
  {f g : ℝ → ℝ} {x : ℝ}
  (hf' : DifferentiableAt ℝ f x)
  (hg' : DifferentiableAt ℝ g x)
  (hg'_ne_0 : deriv g x ≠ 0)
  (f0 : f x = 0) (g0 : g x = 0) :
  Tendsto (λ t => f t / g t) (𝓝[≠] x) (𝓝 (deriv f x / deriv g x)) := by
  classical
  -- Step 1: Convert differentiability information into slope limits for both numerator and denominator.
  have hf_deriv : HasDerivAt f (deriv f x) x := hf'.hasDerivAt
  have hg_deriv : HasDerivAt g (deriv g x) x := hg'.hasDerivAt
  have hf_slope : Tendsto (slope f x) (𝓝[≠] x) (𝓝 (deriv f x)) :=
    (hasDerivAt_iff_tendsto_slope.mp hf_deriv)
  have hg_slope : Tendsto (slope g x) (𝓝[≠] x) (𝓝 (deriv g x)) :=
    (hasDerivAt_iff_tendsto_slope.mp hg_deriv)
  -- Step 2: Use continuity of inversion and multiplication to get the limit for the ratio of slopes.
  have h_slope_ratio :
      Tendsto (fun t => slope f x t / slope g x t) (𝓝[≠] x)
        (𝓝 (deriv f x / deriv g x)) := by
    have hmul :=
      hf_slope.mul ((hg_slope.inv₀ hg'_ne_0))
    simpa [div_eq_mul_inv] using hmul
  -- Step 3: Show that away from `x`, the raw quotient agrees with the slope ratio.
  have h_ne : ∀ᶠ t in 𝓝[≠] x, t ≠ x := by
    have : ({x}ᶜ : Set ℝ) ∈ 𝓝[{x}ᶜ] x := self_mem_nhdsWithin
    simpa [Filter.Eventually, Set.mem_setOf_eq] using this
  have h_eventually_eq :
      (fun t => f t / g t) =ᶠ[𝓝[≠] x] fun t => slope f x t / slope g x t := by
    refine h_ne.mono ?_
    intro t ht
    -- Step 3.1: Rewrite `f t` and `g t` using the slope identity because `t ≠ x` and `f x = g x = 0`.
    have htx : t - x ≠ 0 := sub_ne_zero_of_ne ht
    have hf_expanded : f t = (t - x) * slope f x t := by
      have hf_prod : (t - x) * slope f x t = f t - f x := by
        have hf_formula : slope f x t = (f t - f x) / (t - x) :=
          by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              (slope_def_field (f := f) (a := x) (b := t))
        simpa [hf_formula] using (mul_div_cancel₀ (a := f t - f x) (b := t - x) htx)
      have hf_add : f t = f t - f x + f x := (sub_add_cancel (f t) (f x)).symm
      calc
        f t = f t - f x + f x := hf_add
        _ = (t - x) * slope f x t + f x := by simp [hf_prod]
        _ = (t - x) * slope f x t := by simp [f0]
    have hg_expanded : g t = (t - x) * slope g x t := by
      have hg_prod : (t - x) * slope g x t = g t - g x := by
        have hg_formula : slope g x t = (g t - g x) / (t - x) :=
          by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              (slope_def_field (f := g) (a := x) (b := t))
        simpa [hg_formula] using (mul_div_cancel₀ (a := g t - g x) (b := t - x) htx)
      have hg_add : g t = g t - g x + g x := (sub_add_cancel (g t) (g x)).symm
      calc
        g t = g t - g x + g x := hg_add
        _ = (t - x) * slope g x t + g x := by simp [hg_prod]
        _ = (t - x) * slope g x t := by simp [g0]
    -- Step 3.2: Cancel the common factor `(t - x)` in the quotient.
    calc
      f t / g t = ((t - x) * slope f x t) / ((t - x) * slope g x t) := by
        simp [hf_expanded, hg_expanded]
      _ = slope f x t / slope g x t := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (mul_div_mul_left (a := slope f x t) (b := slope g x t) (c := t - x) htx)
  -- Step 4: Transfer the slope-limit result back to the original quotient via eventual equality.
  exact (tendsto_congr' h_eventually_eq).2 h_slope_ratio
