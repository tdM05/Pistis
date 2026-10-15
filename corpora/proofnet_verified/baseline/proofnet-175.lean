import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators


/-Informal Statement

Suppose $a \in R^{1}, f$ is a twice-differentiable real function on $(a, \infty)$, and $M_{0}, M_{1}, M_{2}$ are the least upper bounds of $|f(x)|,\left|f^{\prime}(x)\right|,\left|f^{\prime \prime}(x)\right|$, respectively, on $(a, \infty)$. Prove that $M_{1}^{2} \leq 4 M_{0} M_{2} .$
-/

/-Informal Proof

The inequality is obvious if $M_0=+\infty$ or $M_2=+\infty$, so we shall assume that $M_0$ and $M_2$ are both finite. We need to show that
$$
\left|f^{\prime}(x)\right| \leq 2 \sqrt{M_0 M_2}
$$
for all $x>a$. We note that this is obvious if $M_2=0$, since in that case $f^{\prime}(x)$ is constant, $f(x)$ is a linear function, and the only bounded linear function is a constant, whose derivative is zero. Hence we shall assume from now on that $0<M_2<+\infty$ and $0<M_0<+\infty$.
Following the hint, we need only choose $h=\sqrt{\frac{M_0}{M_2}}$, and we obtain
$$
\left|f^{\prime}(x)\right| \leq 2 \sqrt{M_0 M_2},
$$
which is precisely the desired inequality.
The case of equality follows, since the example proposed satisfies
$$
f(x)=1-\frac{2}{x^2+1}
$$
for $x \geq 0$. We see easily that $|f(x)| \leq 1$ for all $x>-1$. Now $f^{\prime}(x)=\frac{4 x}{\left(x^2+1\right)^2}$ for $x>0$ and $f^{\prime}(x)=4 x$ for $x<0$. It thus follows from Exercise 9 above that $f^{\prime}(0)=0$, and that $f^{\prime}(x)$ is continuous. Likewise $f^{\prime \prime}(x)=4$ for $x<0$ and $f^{\prime \prime}(x)=\frac{4-4 x^2}{\left(x^2+1\right)^3}=-4 \frac{x^2-1}{\left(x^2+1\right)^3}$. This shows that $\left|f^{\prime \prime}(x)\right|<4$ for $x>0$ and also that $\lim _{x \rightarrow 0} f^{\prime \prime}(x)=4$. Hence Exercise 9 again implies that $f^{\prime \prime}(x)$ is continuous and $f^{\prime \prime}(0)=4$.

On $n$-dimensional space let $\mathbf{f}(x)=\left(f_1(x), \ldots, f_n(x)\right), M_0=\sup |\mathbf{f}(x)|$, $M_1=\sup \left|\mathbf{f}^{\prime}(x)\right|$, and $M_2=\sup \left|\mathbf{f}^{\prime \prime}(x)\right|$. Just as in the numerical case, there is nothing to prove if $M_2=0$ or $M_0=+\infty$ or $M_2=+\infty$, and so we assume $0<M_0<+\infty$ and $0<M_2<\infty$. Let $a$ be any positive number less than $M_1$, let $x_0$ be such that $\left|\mathbf{f}^{\prime}\left(x_0\right)\right|>a$, and let $\mathbf{u}=\frac{1}{\left|\mathbf{f}^{\prime}\left(x_0\right)\right|} \mathbf{f}^{\prime}\left(x_0\right)$. Consider the real-valued function $\varphi(x)=\mathrm{u} \cdot \mathrm{f}(x)$. Let $N_0, N_1$, and $N_2$ be the suprema of $|\varphi(x)|,\left|\varphi^{\prime}(x)\right|$, and $\left|\varphi^{\prime \prime}(x)\right|$ respectively. By the Schwarz inequality we have (since $|\mathbf{u}|=1) N_0 \leq M_0$ and $N_2 \leq M_2$, while $N_1 \geq \varphi\left(x_0\right)=\left|\mathbf{f}^{\prime}\left(x_0\right)\right|>a$. We therefore have $a^2<4 N_0 N_2 \leq 4 M_0 M_2$. Since $a$ was any positive number less than $M_1$, we have $M_1^2 \leq 4 M_0 M_2$, i.e., the result holds also for vector-valued functions.

Equality can hold on any $R^n$, as we see by taking $\mathbf{f}(x)=(f(x), 0, \ldots, 0)$ or $\mathbf{f}(x)=(f(x), f(x), \ldots, f(x))$, where $f(x)$ is a real-valued function for which equality holds.
-/

theorem Rudin_exercise_5_15 {f : ℝ → ℝ} (a M0 M1 M2 : ℝ)
  (hf' : DifferentiableOn ℝ f (Set.Ioi a))
  (hf'' : DifferentiableOn ℝ (deriv f) (Set.Ioi a))
  (hM0 : M0 = sSup {(|f x|) | x ∈ (Set.Ioi a)})
  (hM1 : M1 = sSup {(|deriv f x|) | x ∈ (Set.Ioi a)})
  (hM2 : M2 = sSup {(|deriv (deriv f) x|) | x ∈ (Set.Ioi a)}) :
  (M1 ^ 2) ≤ 4 * M0 * M2 := by
  sorry

/-
Why the formalized statement is false
-------------------------------------
The Lean statement does **not** assume the sets whose suprema are `M0`, `M1`, and `M2` are
bounded above. In ℝ, the supremum of an unbounded set is defined to be `0`, so for an
unbounded function the recorded “least upper bound” can collapse to `0`, breaking the
intended inequality.

Take `f x = x` on `(0, ∞)`. Then
* `|f x| = x` is unbounded above, so `sSup { |f x| | x > 0 } = 0` (by convention).
* `deriv f = 1`, so `sSup { |deriv f x| | x > 0 } = 1`.
* `deriv (deriv f) = 0`, so `sSup { |deriv (deriv f) x| | x > 0 } = 0`.
With `M0 = 0`, `M1 = 1`, `M2 = 0`, the conclusion would read `1 ≤ 0`, which is false.
-/

theorem Rudin_exercise_5_15_neg :
    ∃ (f : ℝ → ℝ) (a M0 M1 M2 : ℝ),
      DifferentiableOn ℝ f (Set.Ioi a) ∧
      DifferentiableOn ℝ (deriv f) (Set.Ioi a) ∧
      M0 = sSup {(|f x|) | x ∈ (Set.Ioi a)} ∧
      M1 = sSup {(|deriv f x|) | x ∈ (Set.Ioi a)} ∧
      M2 = sSup {(|deriv (deriv f) x|) | x ∈ (Set.Ioi a)} ∧
      ¬ (M1 ^ 2 ≤ 4 * M0 * M2) := by
  classical
  -- Step 1: Fix the explicit counterexample data `f x = x`, `a = 0`, `M0 = 0`, `M1 = 1`, `M2 = 0`.
  refine ⟨(fun x : ℝ => x), (0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), ?_⟩
  -- Step 2.1: Show `f` itself is differentiable on `(0, ∞)`.
  have hdiff :
      DifferentiableOn ℝ (fun x : ℝ => x) (Set.Ioi (0 : ℝ)) := by
    simpa using
      (differentiableOn_id : DifferentiableOn ℝ (fun x : ℝ => x) (Set.Ioi (0 : ℝ)))
  -- Step 2.2: Identify `f'` as the constant function `1`, hence differentiable on `(0, ∞)`.
  have hdiff' :
      DifferentiableOn ℝ (deriv fun x : ℝ => x) (Set.Ioi (0 : ℝ)) := by
    have hconst : deriv (fun x : ℝ => x) = fun _ => (1 : ℝ) := by
      funext x; simp
    -- Step 2.2.1: Use the explicit constant description to discharge differentiability.
    simp [hconst, differentiableOn_const]
  -- Step 3.1: Name the three sets of absolute values that occur in the `sSup` hypotheses.
  let S0 : Set ℝ := { |(fun x : ℝ => x) t| | t ∈ Set.Ioi (0 : ℝ) }
  let S1 : Set ℝ := { |(fun _ : ℝ => (1 : ℝ)) t| | t ∈ Set.Ioi (0 : ℝ) }
  let S2 : Set ℝ := { |(fun _ : ℝ => (0 : ℝ)) t| | t ∈ Set.Ioi (0 : ℝ) }
  -- Step 3.2: Identify the image of `(0, ∞)` under `x ↦ |x|` (it is again `(0, ∞)`).
  have hSet0 : S0 = Set.Ioi (0 : ℝ) := by
    ext y; constructor
    · rintro ⟨t, ht, rfl⟩
      have ht_pos : (0 : ℝ) < t := ht
      simpa [abs_of_pos ht_pos] using ht
    · intro hy
      have hy_pos : (0 : ℝ) < y := hy
      refine ⟨y, hy, by simp [abs_of_pos hy_pos]⟩
  -- Step 3.3: Because `(0, ∞)` is unbounded above, its supremum is `0` by convention.
  have hSup0 : sSup S0 = (0 : ℝ) := by
    have hUnbdd : ¬ BddAbove (Set.Ioi (0 : ℝ)) := by
      simpa using (not_bddAbove_Ioi (a := (0 : ℝ)))
    have hSupIoi : sSup (Set.Ioi (0 : ℝ)) = (0 : ℝ) := Real.sSup_of_not_bddAbove hUnbdd
    simpa [S0, hSet0] using hSupIoi
  -- Step 3.4: The set of values of `|f'|` is the singleton `{1}`, whose supremum is `1`.
  have hSup1 : sSup S1 = (1 : ℝ) := by
    have hSingleton : S1 = {(1 : ℝ)} := by
      ext y; constructor
      · rintro ⟨t, ht, rfl⟩; simp
      · intro hy; rcases hy with rfl; refine ⟨1, by norm_num, by simp⟩
    simp [hSingleton]
  -- Step 3.5: The set of values of `|f''|` is constantly `0`, so its supremum is `0`.
  have hSup2 : sSup S2 = (0 : ℝ) := by
    have hSingletonZero : S2 = {(0 : ℝ)} := by
      ext y; constructor
      · rintro ⟨t, ht, rfl⟩; simp
      · intro hy; rcases hy with rfl; refine ⟨1, by norm_num, by simp⟩
    simp [hSingletonZero]
  -- Step 4: Assemble the long conjunction of hypotheses using the computed facts.
  refine And.intro hdiff ?_
  refine And.intro hdiff' ?_
  refine And.intro (by simpa [S0] using hSup0.symm) ?_
  refine And.intro (by simpa [S1] using hSup1.symm) ?_
  refine And.intro (by simpa [S2] using hSup2.symm) ?_
  -- Step 5: Under our choices, the inequality reads `1 ≤ 0`, which is impossible.
  norm_num

/-
Corrected version
-----------------
The genuine fix is to add the three missing boundedness assumptions — without them,
`sSup` of an unbounded set silently collapses to `0` (the diagnosis used in `_neg`
above).  The previous corrected version went further and *also* assumed `M1 = 0`,
`M2 = 0`, and `0 ≤ M0`, which trivializes the inequality to `0 ≤ 0` and proves
nothing about Landau's theorem.  Those trivializing hypotheses are removed here,
and the conclusion is now the genuine Landau / Kolmogorov inequality
`M1 ^ 2 ≤ 4 * M0 * M2`.

Proof strategy: Taylor's theorem at order 2 gives, for every `x ∈ (a, ∞)` and
`h > 0`, an `ξ ∈ (x, x + 2h)` with
    f(x + 2h) = f(x) + 2h · f'(x) + 2h² · f''(ξ).
Solving for `f'(x)` and taking absolute values yields the pointwise bound
`|f'(x)| ≤ M0 / h + h · M2`.  Taking `sSup` over `x` gives `M1 ≤ M0/h + h M2`
for every `h > 0`.  Choosing `h = √(M0/M2)` (when both are positive) makes the
right-hand side equal `2√(M0 M2)`, hence `M1 ^ 2 ≤ 4 · M0 · M2`.  The edge
cases `M2 = 0` (force `M1 = 0` by sending `h → ∞`) and `M0 = 0` (force `f ≡ 0`,
hence `M1 = 0`) are handled separately.
-/

namespace Landau175

-- A1: derivWithin (Icc x y) f = deriv f at points of Ioo x y.
private lemma derivWithin_Icc_eq_deriv {f : ℝ → ℝ} {x y t : ℝ} (ht : t ∈ Set.Ioo x y) :
    derivWithin f (Set.Icc x y) t = deriv f t := by
  apply derivWithin_of_mem_nhds
  exact mem_of_superset (isOpen_Ioo.mem_nhds ht) Set.Ioo_subset_Icc_self

-- A2: ContDiffOn ℝ 1 f s on an open set ⟸ DifferentiableOn ∧ DifferentiableOn (deriv f).
private lemma contDiffOn_one_of_differentiableOn_open
    {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hf : DifferentiableOn ℝ f s) (hf' : DifferentiableOn ℝ (deriv f) s) :
    ContDiffOn ℝ 1 f s := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl,
      contDiffOn_succ_iff_deriv_of_isOpen hs]
  refine ⟨hf, ?_, ?_⟩
  · intro h; exact absurd h (by decide)
  · exact contDiffOn_zero.mpr hf'.continuousOn

-- B: The key second-order Taylor expansion for our setting.
private lemma taylor_two {f : ℝ → ℝ} {a x h : ℝ}
    (hf : DifferentiableOn ℝ f (Set.Ioi a))
    (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi a))
    (hx : a < x) (hh : 0 < h) :
    ∃ ξ ∈ Set.Ioo x (x + 2*h),
      f (x + 2*h) = f x + 2*h * deriv f x + 2*h^2 * deriv (deriv f) ξ := by
  -- Step 1: Set up the closed interval [x, x + 2h] ⊂ (a, ∞).
  set y := x + 2 * h with hy_def
  have hxy : x < y := by rw [hy_def]; linarith
  have h_y_sub_x : y - x = 2 * h := by rw [hy_def]; ring
  have hIcc_sub : Set.Icc x y ⊆ Set.Ioi a := fun t ht => lt_of_lt_of_le hx ht.1
  have hIoo_sub : Set.Ioo x y ⊆ Set.Ioi a := fun t ht => lt_of_lt_of_le hx (le_of_lt ht.1)
  -- Step 2: Establish ContDiffOn ℝ 1 on the closed interval.
  have h_cont1_open : ContDiffOn ℝ 1 f (Set.Ioi a) :=
    contDiffOn_one_of_differentiableOn_open isOpen_Ioi hf hf'
  have h_cont1 : ContDiffOn ℝ 1 f (Set.Icc x y) := h_cont1_open.mono hIcc_sub
  -- Step 3: iteratedDerivWithin 1 f (Icc x y) is differentiable on Ioo x y.
  have h_diff_idw : DifferentiableOn ℝ
      (iteratedDerivWithin 1 f (Set.Icc x y)) (Set.Ioo x y) := by
    have h_diff_deriv : DifferentiableOn ℝ (deriv f) (Set.Ioo x y) := hf'.mono hIoo_sub
    refine h_diff_deriv.congr ?_
    intro t ht
    rw [iteratedDerivWithin_one]
    exact derivWithin_Icc_eq_deriv ht
  -- Step 4: Apply Mathlib's Taylor remainder.
  obtain ⟨ξ, hξ, hT⟩ :=
    taylor_mean_remainder_lagrange (f := f) (x := y) (x₀ := x) (n := 1) hxy h_cont1 h_diff_idw
  refine ⟨ξ, hξ, ?_⟩
  -- Step 5: Unpack taylorWithinEval f 1 (Icc x y) x y = f x + 2h * deriv f x.
  have h_t1 : taylorWithinEval f 1 (Set.Icc x y) x y = f x + 2 * h * deriv f x := by
    rw [taylor_within_apply]
    simp [Finset.sum_range_succ, iteratedDerivWithin_zero, iteratedDerivWithin_one,
          Nat.factorial]
    have h_dW : derivWithin f (Set.Icc x y) x = deriv f x := by
      have h_diff : DifferentiableAt ℝ f x :=
        (hf x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)
      have h_unique : UniqueDiffWithinAt ℝ (Set.Icc x y) x :=
        (uniqueDiffOn_Icc hxy) x (Set.left_mem_Icc.mpr hxy.le)
      exact h_diff.derivWithin h_unique
    rw [h_dW, h_y_sub_x]
  -- Step 6: Unpack iteratedDerivWithin 2 f (Icc x y) ξ = deriv (deriv f) ξ.
  have h_idw2 : iteratedDerivWithin 2 f (Set.Icc x y) ξ = deriv (deriv f) ξ := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDerivWithin_succ, iteratedDerivWithin_one]
    have h_outer : derivWithin (derivWithin f (Set.Icc x y)) (Set.Icc x y) ξ
                    = deriv (derivWithin f (Set.Icc x y)) ξ := by
      apply derivWithin_of_mem_nhds
      exact mem_of_superset (isOpen_Ioo.mem_nhds hξ) Set.Ioo_subset_Icc_self
    rw [h_outer]
    have h_eqOn : (fun t => derivWithin f (Set.Icc x y) t) =ᶠ[𝓝 ξ] (fun t => deriv f t) := by
      filter_upwards [isOpen_Ioo.mem_nhds hξ] with t ht
      exact derivWithin_Icc_eq_deriv ht
    exact h_eqOn.deriv_eq
  -- Step 7: Substitute into the Taylor identity and simplify.
  rw [h_idw2] at hT
  rw [h_t1] at hT
  have h_pow : (y - x)^(1+1) = (2*h)^2 := by rw [h_y_sub_x]
  rw [h_pow] at hT
  have h_fact : ((1 + 1 : ℕ).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [h_fact] at hT
  have : f (x + 2*h) = f x + 2 * h * deriv f x + (deriv (deriv f) ξ) * (2*h)^2 / 2 := by
    linarith [hT]
  rw [this]; ring

-- C: |f x| ≤ M when M is the sSup of the absolute value image.
private lemma le_sup_of_bdd {f : ℝ → ℝ} {a M : ℝ}
    (hbdd : BddAbove {(|f x|) | x ∈ Set.Ioi a})
    (hM : M = sSup {(|f x|) | x ∈ Set.Ioi a})
    {x : ℝ} (hx : x ∈ Set.Ioi a) : |f x| ≤ M := by
  rw [hM]; exact le_csSup hbdd ⟨x, hx, rfl⟩

-- D: such an `M` is automatically nonneg (witness via `a + 1`).
private lemma sup_nonneg_of_bdd {f : ℝ → ℝ} {a M : ℝ}
    (hbdd : BddAbove {(|f x|) | x ∈ Set.Ioi a})
    (hM : M = sSup {(|f x|) | x ∈ Set.Ioi a}) : 0 ≤ M :=
  le_trans (abs_nonneg _) (le_sup_of_bdd hbdd hM (show a + 1 ∈ Set.Ioi a by simp))

-- E: pointwise bound `|f'(x)| ≤ M0/h + h*M2` from the Taylor identity.
private lemma pointwise_bound {f : ℝ → ℝ} {a M0 M2 : ℝ}
    (hf : DifferentiableOn ℝ f (Set.Ioi a))
    (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi a))
    (hbdd0 : BddAbove {(|f x|) | x ∈ Set.Ioi a})
    (hbdd2 : BddAbove {(|deriv (deriv f) x|) | x ∈ Set.Ioi a})
    (hM0 : M0 = sSup {(|f x|) | x ∈ Set.Ioi a})
    (hM2 : M2 = sSup {(|deriv (deriv f) x|) | x ∈ Set.Ioi a})
    {x : ℝ} (hx : x ∈ Set.Ioi a) {h : ℝ} (hh : 0 < h) :
    |deriv f x| ≤ M0 / h + h * M2 := by
  -- Step 1: Apply Taylor.
  have hxa : a < x := hx
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ := taylor_two hf hf' hxa hh
  have h2h_pos : (0 : ℝ) < 2 * h := by linarith
  -- Step 2: Solve the Taylor identity for `deriv f x`.
  have h_solve : deriv f x = (f (x + 2*h) - f x - 2*h^2 * deriv (deriv f) ξ) / (2*h) := by
    field_simp
    linarith
  -- Step 3: ξ and x + 2h are still in (a, ∞), so the bounds apply.
  have hξ_in : ξ ∈ Set.Ioi a := lt_trans hxa hξ_mem.1
  have hx2h_in : x + 2*h ∈ Set.Ioi a := by rw [Set.mem_Ioi]; linarith
  have h_fx_bd : |f x| ≤ M0 := le_sup_of_bdd hbdd0 hM0 hx
  have h_fx2h_bd : |f (x + 2*h)| ≤ M0 := le_sup_of_bdd hbdd0 hM0 hx2h_in
  have h_fpp_bd : |deriv (deriv f) ξ| ≤ M2 := le_sup_of_bdd hbdd2 hM2 hξ_in
  -- Step 4: Bound the numerator by 2 M0 + 2h² M2.
  have h_num_bd :
      |f (x + 2*h) - f x - 2*h^2 * deriv (deriv f) ξ| ≤ 2*M0 + 2*h^2 * M2 := by
    have h1 : |f (x + 2*h) - f x - 2*h^2 * deriv (deriv f) ξ|
              ≤ |f (x + 2*h)| + |f x| + |2*h^2 * deriv (deriv f) ξ| := by
      have h_step : |f (x + 2*h) - f x - 2*h^2 * deriv (deriv f) ξ|
              ≤ |f (x + 2*h) - f x| + |2*h^2 * deriv (deriv f) ξ| := by
        have h_split : f (x + 2*h) - f x - 2*h^2 * deriv (deriv f) ξ
                     = (f (x + 2*h) - f x) + (-(2*h^2 * deriv (deriv f) ξ)) := by ring
        rw [h_split]
        have := abs_add_le (f (x + 2*h) - f x) (-(2*h^2 * deriv (deriv f) ξ))
        rw [abs_neg] at this
        exact this
      have hsub := abs_sub (f (x + 2*h)) (f x)
      linarith
    have h2 : |2*h^2 * deriv (deriv f) ξ| = 2*h^2 * |deriv (deriv f) ξ| := by
      rw [abs_mul, abs_of_pos (show (0 : ℝ) < 2*h^2 by positivity)]
    have h2h2_nn : 0 ≤ 2 * h^2 := by positivity
    nlinarith [h_fx_bd, h_fx2h_bd, h_fpp_bd]
  -- Step 5: Divide by 2h.
  rw [h_solve, abs_div, abs_of_pos h2h_pos]
  rw [div_le_iff₀ h2h_pos]
  have h_rhs : (M0 / h + h * M2) * (2 * h) = 2*M0 + 2*h^2 * M2 := by field_simp
  rw [h_rhs]
  exact h_num_bd

-- F: lift to a sup bound: M1 ≤ M0/h + h*M2 for all h > 0.
private lemma sup_bound {f : ℝ → ℝ} {a M0 M1 M2 : ℝ}
    (hf : DifferentiableOn ℝ f (Set.Ioi a))
    (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi a))
    (hbdd0 : BddAbove {(|f x|) | x ∈ Set.Ioi a})
    (_hbdd1 : BddAbove {(|deriv f x|) | x ∈ Set.Ioi a})
    (hbdd2 : BddAbove {(|deriv (deriv f) x|) | x ∈ Set.Ioi a})
    (hM0 : M0 = sSup {(|f x|) | x ∈ Set.Ioi a})
    (hM1 : M1 = sSup {(|deriv f x|) | x ∈ Set.Ioi a})
    (hM2 : M2 = sSup {(|deriv (deriv f) x|) | x ∈ Set.Ioi a})
    {h : ℝ} (hh : 0 < h) :
    M1 ≤ M0 / h + h * M2 := by
  rw [hM1]
  apply csSup_le
  · exact ⟨|deriv f (a + 1)|, a + 1, by simp, rfl⟩
  · rintro y ⟨x, hx, rfl⟩
    exact pointwise_bound hf hf' hbdd0 hbdd2 hM0 hM2 hx hh

end Landau175

theorem Rudin_exercise_5_15_corrected
    {f : ℝ → ℝ} {a M0 M1 M2 : ℝ}
    (hf' : DifferentiableOn ℝ f (Set.Ioi a))
    (hf'' : DifferentiableOn ℝ (deriv f) (Set.Ioi a))
    (hbdd0 : BddAbove {(|f x|) | x ∈ (Set.Ioi a)})
    (hbdd1 : BddAbove {(|deriv f x|) | x ∈ (Set.Ioi a)})
    (hbdd2 : BddAbove {(|deriv (deriv f) x|) | x ∈ (Set.Ioi a)})
    (hM0 : M0 = sSup {(|f x|) | x ∈ (Set.Ioi a)})
    (hM1 : M1 = sSup {(|deriv f x|) | x ∈ (Set.Ioi a)})
    (hM2 : M2 = sSup {(|deriv (deriv f) x|) | x ∈ (Set.Ioi a)}) :
    (M1 ^ 2) ≤ 4 * M0 * M2 := by
  -- Step 1: Establish nonnegativity of all three sups.
  have hM0_nn : 0 ≤ M0 := Landau175.sup_nonneg_of_bdd hbdd0 hM0
  have hM1_nn : 0 ≤ M1 := Landau175.sup_nonneg_of_bdd hbdd1 hM1
  have hM2_nn : 0 ≤ M2 := Landau175.sup_nonneg_of_bdd hbdd2 hM2
  -- Step 2: Case-split on whether M2 = 0.
  rcases eq_or_lt_of_le hM2_nn with hM2_zero | hM2_pos
  · -- Step 2.A (M2 = 0): the sup bound gives `M1 ≤ M0 / h` for every h > 0; let h → ∞
    -- to force M1 = 0.
    have hM2_eq : M2 = 0 := hM2_zero.symm
    have hM1_zero : M1 = 0 := by
      by_contra h_ne
      have hM1_pos : 0 < M1 := lt_of_le_of_ne hM1_nn (Ne.symm h_ne)
      -- Pick h large enough that M0 / h < M1.
      set h := 2 * M0 / M1 + 1 with hh_def
      have hh_pos : 0 < h := by positivity
      have h_ineq : M1 ≤ M0 / h + h * M2 :=
        Landau175.sup_bound hf' hf'' hbdd0 hbdd1 hbdd2 hM0 hM1 hM2 hh_pos
      rw [hM2_eq] at h_ineq
      simp at h_ineq
      have h_M1h : M1 * h = 2*M0 + M1 := by rw [hh_def]; field_simp
      have : M0 / h < M1 := by
        rw [div_lt_iff₀ hh_pos]
        nlinarith [hM0_nn, hM1_pos, h_M1h]
      linarith
    rw [hM1_zero, hM2_eq]; ring_nf; positivity
  · -- Step 2.B (M2 > 0): case-split further on M0.
    rcases eq_or_lt_of_le hM0_nn with hM0_zero | hM0_pos
    · -- Step 2.B.i (M0 = 0): then |f x| ≤ 0 on Ioi a forces f ≡ 0, hence f' = 0, M1 = 0.
      have hM0_eq : M0 = 0 := hM0_zero.symm
      have hf_zero : ∀ x ∈ Set.Ioi a, f x = 0 := by
        intro x hx
        have h_le : |f x| ≤ M0 := Landau175.le_sup_of_bdd hbdd0 hM0 hx
        rw [hM0_eq] at h_le
        exact abs_eq_zero.mp (le_antisymm h_le (abs_nonneg _))
      have h_deriv_zero : ∀ x ∈ Set.Ioi a, deriv f x = 0 := by
        intro x hx
        have h_eqOn : f =ᶠ[𝓝 x] (fun _ => 0) := by
          filter_upwards [isOpen_Ioi.mem_nhds hx] with t ht
          exact hf_zero t ht
        rw [h_eqOn.deriv_eq]
        simp
      have hM1_zero : M1 = 0 := by
        rw [hM1]
        apply le_antisymm
        · apply csSup_le
          · refine ⟨0, a + 1, ?_, ?_⟩
            · simp
            · rw [h_deriv_zero (a + 1) (by simp)]; simp
          · rintro y ⟨x, hx, rfl⟩
            rw [h_deriv_zero x hx]; simp
        · have h_in : (0 : ℝ) ∈ {(|deriv f x|) | x ∈ Set.Ioi a} := by
            refine ⟨a + 1, by simp, ?_⟩
            rw [h_deriv_zero (a + 1) (by simp)]; simp
          exact le_csSup hbdd1 h_in
      rw [hM1_zero, hM0_eq]; ring_nf; positivity
    · -- Step 2.B.ii (M0 > 0, M2 > 0): plug `h = √(M0 / M2)` into the sup bound.
      set h := Real.sqrt (M0 / M2) with hh_def
      have hM0M2_pos : 0 < M0 / M2 := div_pos hM0_pos hM2_pos
      have hh_pos : 0 < h := Real.sqrt_pos.mpr hM0M2_pos
      have h_ineq : M1 ≤ M0 / h + h * M2 :=
        Landau175.sup_bound hf' hf'' hbdd0 hbdd1 hbdd2 hM0 hM1 hM2 hh_pos
      -- (M0 / h + h * M2)² = 4 · M0 · M2 when h² · M2 = M0.
      have h_sq_eq : (M0 / h + h * M2) ^ 2 = 4 * M0 * M2 := by
        have h_h_sq : h ^ 2 = M0 / M2 := by
          rw [hh_def]
          exact Real.sq_sqrt hM0M2_pos.le
        have hh_ne : h ≠ 0 := ne_of_gt hh_pos
        have hM2_ne : M2 ≠ 0 := ne_of_gt hM2_pos
        have h_h_sq_M2 : h ^ 2 * M2 = M0 := by rw [h_h_sq]; field_simp
        field_simp
        nlinarith [h_h_sq_M2, sq_nonneg h, hM0_nn, hM2_nn]
      have h_sq_le : M1 ^ 2 ≤ (M0 / h + h * M2) ^ 2 :=
        pow_le_pow_left₀ hM1_nn h_ineq 2
      linarith [h_sq_eq]
