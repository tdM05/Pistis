import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology



/-Informal Statement

Suppose $f$ is an analytic function defined everywhere in $\mathbb{C}$ and such that for each $z_0 \in \mathbb{C}$ at least one coefficient in the expansion $f(z) = \sum_{n=0}^\infty c_n(z - z_0)^n$ is equal to 0. Prove that $f$ is a polynomial.
-/

/-Informal Proof

Say that at least one of the coefficients of the Taylor series vanishes is the same as saying that for every $a \in \mathbb{C}$ there is $m \in \mathbb{N}$ such that $f^{(m)}(a)=0$.
Consider $A_n:=\left\{z \in \mathbb{C}: f^{(n)}(z)=0\right\}$ for each $n \in \mathbb{N}$. Note that:
$f$ is polynomial iff $A_n$ is not countable for some $n \in \mathbb{N}$.
Indeed, if $f$ is polynomial of degree $n$, then $f^{(n+1)}(z)=0$ for all $z \in \mathbb{C}$, then $A_{n+1}=\mathbb{C}$, so, $A_{n+1}$ is not countable. Conversely, if there is $n \in \mathbb{C}$ such that $A_n$ is not countable, then $A_n$ has a limit point, then by Identity principle we have $f^{(n)}(z)=0$ for all $z \in \mathbb{C}$, so, $f$ is a polynomial of degree at most $n-1$.

Therefore, tt suffices to show that there is $n \in \mathbb{N}$ such that $A_n$ is not countable. Indeed, consider $\bigcup_{n \in \mathbb{N}} A_n$, by hypothesis for each $a \in \mathbb{C}$ there is $m \in \mathbb{N}$ such that $f^{(m)}(a)=0$, then $\mathbb{C} \subseteq \bigcup_{n \in \mathbb{N}} A_n$. Therefore, $\bigcup_{n \in \mathbb{N}} A_n$ is not countable, then there is $n \in \mathbb{N}$ such that $A_n$ is not countable.
-/

theorem Shakarchi_exercise_2_13 {f : ℂ → ℂ}
    (hf : ∀ z₀ : ℂ, ∃ (s : Set ℂ) (c : ℕ → ℂ), IsOpen s ∧ z₀ ∈ s ∧
      (∀ z ∈ s, Tendsto (λ n => ∑ i ∈ range n, (c i) * (z - z₀)^i) atTop (𝓝 (f z₀)))
      ∧ ∃ i, c i = 0) :
    ∃ (c : ℕ → ℂ) (n : ℕ), f = λ z => ∑ i ∈ range n, (c i) * z ^ i := by
  sorry

/-
Step 1: Explain why the formalized hypothesis is vacuous and therefore the theorem is false.
Step 2: Build an explicit counterexample function, check that it satisfies the hypothesis, but show
        that it cannot be a polynomial.
Step 3: Prove the negation of the original statement by instantiating it with the counterexample.
-/

open scoped Topology

noncomputable section

private def pathological (z : ℂ) : ℂ :=
  if z = 0 then 0 else 1

@[simp] lemma pathological_zero : pathological 0 = 0 := by
  -- Step 1: Evaluate the definition at `0`.
  simp [pathological]

lemma pathological_ne_zero {z : ℂ} (hz : z ≠ 0) : pathological z = 1 := by
  -- Step 1: Use the defining if-then-else with the hypothesis `z ≠ 0`.
  simp [pathological, hz]

lemma constant_series_sum (a z z₀ : ℂ) :
    ∀ k : ℕ, ∑ i ∈ range (k + 1), (if i = 0 then a else 0) * (z - z₀) ^ i = a := by
  -- Step 1: Reduce to a combinatorial statement about finite sets.
  classical
  -- Step 1.1: Prove an auxiliary formula for arbitrary finite sets.
  have aux :
      ∀ s : Finset ℕ,
        ∑ i ∈ s, (if i = 0 then a else 0) * (z - z₀) ^ i =
          (if (0 : ℕ) ∈ s then a else 0) := by
    -- Step 1.1.1: Induct on `s`.
    intro s
    refine Finset.induction_on s ?base ?step
    · -- Base case: the empty set.
      simp
    · intro i s hi ih
      -- Step 1.1.2: Distinguish whether the newly inserted element is `0`.
      by_cases hzero : i = 0
      · subst hzero
        simp [hi]
      · simp
  intro k
  -- Step 2: The range always contains `0`, so the auxiliary formula yields `a`.
  have hmem : (0 : ℕ) ∈ range (k + 1) := by
    have : 0 < k + 1 := Nat.succ_pos _
    exact Finset.mem_range.mpr this
  simp [hmem]

lemma constant_series_eventually_constant (a z z₀ : ℂ) :
    (fun n : ℕ => ∑ i ∈ range n, (if i = 0 then a else 0) * (z - z₀) ^ i)
        =ᶠ[atTop] fun _ => a := by
  -- Step 1: Show the partial sums stabilize at `a` once `0` is included.
  refine Filter.eventually_atTop.mpr ?_
  refine ⟨1, ?_⟩
  intro n hn
  -- Step 1.1: Rewrite `n` as `k + 1`.
  have hn' : 0 < n := Nat.succ_le_iff.mp hn
  have hn0 : n ≠ 0 := ne_of_gt hn'
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  -- Step 1.2: Apply the closed-form expression.
  simp

lemma constant_series_tendsto (a z z₀ : ℂ) :
    Tendsto (fun n : ℕ => ∑ i ∈ range n, (if i = 0 then a else 0) * (z - z₀) ^ i)
      atTop (𝓝 a) := by
  -- Step 1: The sequence becomes constant, so it converges to that constant.
  refine (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) _ _).congr' ?_
  -- Step 1.1: Use the eventual equality from the previous lemma.
  exact (constant_series_eventually_constant a z z₀).symm

lemma all_functions_satisfy_hypothesis {f : ℂ → ℂ} :
    ∀ z₀ : ℂ, ∃ (s : Set ℂ) (c : ℕ → ℂ),
      IsOpen s ∧ z₀ ∈ s ∧
        (∀ z ∈ s,
          Tendsto (fun n : ℕ => ∑ i ∈ range n, (c i) * (z - z₀) ^ i)
            atTop (𝓝 (f z₀))) ∧
        ∃ i, c i = 0 := by
  -- Step 1: Fix an arbitrary point `z₀`.
  intro z₀
  -- Step 2: Take the whole plane as the open set and use a constant series.
  refine ⟨Set.univ, fun n => if n = 0 then f z₀ else 0, isOpen_univ, trivial, ?_, ?_⟩
  · -- Step 2.1: Show the constructed series converges to `f z₀` for every `z`.
    intro z _
    -- Step 2.1.1: Apply the constant-series lemma.
    simpa using constant_series_tendsto (f z₀) z z₀
  · -- Step 2.2: Exhibit a zero coefficient (at index `1`).
    refine ⟨1, ?_⟩
    simp

lemma polynomial_sum_continuous (c : ℕ → ℂ) (n : ℕ) :
    Continuous fun z : ℂ => ∑ i ∈ range n, c i * z ^ i := by
  -- Step 1: Finite sums of continuous functions remain continuous.
  classical
  refine continuous_finset_sum _ ?_
  intro i _
  -- Step 1.1: Each summand is a constant multiple of `z ↦ z^i`.
  exact (continuous_const.mul ((continuous_id).pow _))

lemma pathological_not_continuous :
    ¬ ContinuousAt pathological 0 := by
  -- Step 1: Assume, for contradiction, that the function is continuous at `0`.
  intro hcont
  -- Step 2: Consider the ball of radius `1/2` around `0`.
  have hball :
      Metric.ball (0 : ℂ) (1 / 2 : ℝ) ∈ 𝓝 (pathological 0) := by
    simpa [pathological_zero] using
      Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)
  -- Step 3: Pull back this neighborhood via `pathological`.
  have hpre : pathological ⁻¹' Metric.ball (0 : ℂ) (1 / 2 : ℝ) ∈ 𝓝 (0 : ℂ) :=
    (show Tendsto pathological (𝓝 0) (𝓝 (pathological 0)) from hcont) hball
  -- Step 4: The preimage is just `{0}`.
  have hset :
      pathological ⁻¹' Metric.ball (0 : ℂ) (1 / 2 : ℝ) = ({0} : Set ℂ) := by
    ext z
    constructor
    · intro hz
      by_contra hzero
      have hdist : dist (pathological z) 0 = 1 := by
        simp [pathological_ne_zero hzero]
      have : (1 : ℝ) < 1 / 2 := by simpa [hdist] using hz
      exact (by norm_num : ¬ (1 : ℝ) < 1 / 2) this
    · rintro rfl
      simp [pathological_zero, Metric.mem_ball]
  -- Step 5: Use the neighborhood characterization to find a contradiction.
  rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, ε_pos, hsubset⟩
  have hsubset' : Metric.ball (0 : ℂ) ε ⊆ ({0} : Set ℂ) := by
    intro x hx
    have hx' : x ∈ pathological ⁻¹' Metric.ball (0 : ℂ) (1 / 2 : ℝ) :=
      hsubset hx
    have hx_zero : x = 0 := by
      by_contra hx0
      have hdist : dist (pathological x) 0 = 1 := by
        simp [pathological_ne_zero hx0]
      have : (1 : ℝ) < 1 / 2 := by simpa [hdist] using hx'
      exact (by norm_num : ¬ (1 : ℝ) < 1 / 2) this
    simp [Set.mem_singleton_iff, hx_zero]
  set w : ℂ := (Complex.ofReal (ε / 2)) with hw
  have hw_mem : w ∈ Metric.ball (0 : ℂ) ε := by
    have hnorm' : ‖w‖ = |ε / 2| := by
      simpa [w] using (RCLike.norm_ofReal (K := ℂ) (ε / 2))
    have hnorm : ‖w‖ = ε / 2 := by
      have hpos : 0 < ε / 2 := half_pos ε_pos
      simp [hnorm', abs_of_pos hpos]
    have hdist : dist w (0 : ℂ) = ε / 2 := by
      simp [hnorm]
    simp [Metric.mem_ball, hdist, half_lt_self ε_pos]
  have hw_ne : w ≠ 0 := by
    have : (ε / 2 : ℝ) ≠ 0 := ne_of_gt (half_pos ε_pos)
    simpa [w] using Complex.ofReal_ne_zero.mpr this
  have : w ∈ ({0} : Set ℂ) := hsubset' hw_mem
  have hw_zero : w = 0 := by
    simpa [Set.mem_singleton_iff] using this
  exact hw_ne hw_zero

lemma pathological_not_polynomial :
    ¬ ∃ (c : ℕ → ℂ) (n : ℕ), pathological = λ z => ∑ i ∈ range n, c i * z ^ i := by
  -- Step 1: Assume `pathological` equals a polynomial and derive a contradiction.
  intro hpoly
  -- Step 2: Extract the coefficients and the truncation order.
  rcases hpoly with ⟨c, n, hpoly⟩
  -- Step 3: The polynomial is continuous, hence `pathological` would be continuous.
  have hcont :
      ContinuousAt pathological 0 := by
    -- Step 3.1: Transport continuity along the equality.
    have hpoly_cont := polynomial_sum_continuous c n
    -- Step 3.2: Rewrite via the assumed identity.
    simpa [hpoly] using (hpoly_cont.continuousAt : ContinuousAt _ _)
  -- Step 4: Contradict the explicit discontinuity.
  exact pathological_not_continuous hcont

lemma Shakarchi_exercise_2_13_neg :
    ¬ (∀ f : ℂ → ℂ,
        (∀ z₀ : ℂ, ∃ (s : Set ℂ) (c : ℕ → ℂ), IsOpen s ∧ z₀ ∈ s ∧
          (∀ z ∈ s,
            Tendsto (fun n : ℕ => ∑ i ∈ range n, c i * (z - z₀) ^ i)
              atTop (𝓝 (f z₀))) ∧
          ∃ i, c i = 0) →
        ∃ (c : ℕ → ℂ) (n : ℕ), f = fun z => ∑ i ∈ range n, c i * z ^ i) := by
  -- Step 1: Assume the universal statement holds and reach a contradiction.
  intro h
  -- Step 2: Specialize to the pathological counterexample.
  have hcounter :=
    (all_functions_satisfy_hypothesis (f := pathological))
  -- Step 3: The conclusion would force `pathological` to be a polynomial.
  have hpoly := h pathological hcounter
  -- Step 4: Contradiction with the discontinuity argument.
  exact pathological_not_polynomial hpoly

/-
The original formalization is not faithful to the informal statement.

The informal statement says: f is entire (analytic on all of ℂ), and for each z₀ ∈ ℂ at least
one Taylor coefficient cₙ(z₀) in the expansion around z₀ vanishes. Conclude: f is a polynomial.

The original Lean hypothesis says: for every z₀ there exist an open set s ∋ z₀, coefficients c,
and a vanishing coefficient, such that the series converges to f(z₀) for all z ∈ s. The critical
bug is that the series converges to f(z₀) (the value at the *center*) rather than to f(z) (the
value at the *variable point*). This means the series need not represent f at all — any function
trivially satisfies the hypothesis by using the constant series c₀ = f(z₀), cₙ = 0 for n ≥ 1.
The counterexample and negation proof above demonstrate this.

The correction fixes the hypothesis to faithfully encode:
  (1) f is entire — formalized as `Differentiable ℂ f`.
  (2) For every z₀, at least one Taylor coefficient vanishes —
      formalized literally as
      `∀ z₀, ∃ n, iteratedDeriv n f z₀ / (n.factorial : ℂ) = 0`.
The conclusion is that f is a polynomial, formalized via Mathlib's `Polynomial.aeval`.
-/

theorem Shakarchi_exercise_2_13_corrected
    {f : ℂ → ℂ}
    (hf_diff : Differentiable ℂ f)
    (hf_vanish : ∀ z₀ : ℂ, ∃ n : ℕ,
      iteratedDeriv n f z₀ / (n.factorial : ℂ) = 0) :
    ∃ (p : Polynomial ℂ), f = fun z => Polynomial.aeval z p := by
  classical
  -- Step 1: Convert the literal Taylor-coefficient hypothesis into the derivative-zero form.
  -- Step 1.1: Define the zero set of the `n`-th iterated derivative.
  let Z : ℕ → Set ℂ := fun n => {z : ℂ | iteratedDeriv n f z = 0}

  -- Step 1.2: Since `n!` is nonzero in `ℂ`, a zero Taylor coefficient means
  -- `iteratedDeriv n f z = 0`.
  have hf_vanish_deriv : ∀ z₀ : ℂ, ∃ n : ℕ, iteratedDeriv n f z₀ = 0 := by
    intro z₀
    rcases hf_vanish z₀ with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hfact : (n.factorial : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    exact (div_eq_zero_iff.mp hn).resolve_right hfact

  -- Step 2: Use Baire category to find one derivative order whose zero set has interior.
  -- Step 2.1: Entire functions are smooth, so every iterated derivative is continuous.
  have hf_contDiff : ContDiff ℂ ⊤ f := hf_diff.contDiff

  -- Step 2.2: Each `Z n` is closed as the preimage of `{0}` under a continuous function.
  have hZ_closed : ∀ n : ℕ, IsClosed (Z n) := by
    intro n
    have hcont : Continuous (iteratedDeriv n f) :=
      hf_contDiff.continuous_iteratedDeriv n (by simp)
    simpa [Z] using isClosed_singleton.preimage hcont

  -- Step 2.3: The pointwise vanishing hypothesis says that the closed sets `Z n`
  -- cover the whole complex plane.
  have hZ_cover : (⋃ n : ℕ, Z n) = Set.univ := by
    ext z
    constructor
    · intro _
      trivial
    · intro _
      rcases hf_vanish_deriv z with ⟨n, hn⟩
      exact Set.mem_iUnion.mpr ⟨n, hn⟩

  -- Step 2.4: By Baire's theorem, at least one `Z N` has nonempty interior.
  obtain ⟨N, hN_interior⟩ :=
    nonempty_interior_of_iUnion_of_closed (X := ℂ) (f := Z) hZ_closed hZ_cover

  -- Step 2.5: Choose a point in that interior.
  rcases hN_interior with ⟨w, hw⟩

  -- Step 3: Promote local vanishing of the `N`-th derivative to global vanishing.
  -- Step 3.1: Membership in `interior (Z N)` gives eventual equality to zero near `w`.
  have hN_eventually_zero : iteratedDeriv N f =ᶠ[𝓝 w] (fun _ : ℂ => 0) := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr ?_
    refine ⟨interior (Z N), isOpen_interior.mem_nhds hw, ?_⟩
    intro z hz
    have hzZ : z ∈ Z N := interior_subset hz
    exact hzZ

  -- Step 3.2: The original entire function is analytic on all of `ℂ`.
  have hf_analytic : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf_diff.analyticAt z

  -- Step 3.3: Therefore the `N`-th iterated derivative is analytic on all of `ℂ`.
  have hN_analytic : AnalyticOnNhd ℂ (iteratedDeriv N f) Set.univ := by
    simpa [iteratedDeriv_eq_iterate] using hf_analytic.iterated_deriv N

  -- Step 3.4: The zero function is analytic on all of `ℂ`.
  have hzero_analytic : AnalyticOnNhd ℂ (0 : ℂ → ℂ) Set.univ := analyticOnNhd_const

  -- Step 3.5: The identity principle makes the local equality global.
  have hN_zero_fun : iteratedDeriv N f = (0 : ℂ → ℂ) :=
    hN_analytic.eq_of_eventuallyEq hzero_analytic hN_eventually_zero

  -- Step 4: Build the polynomial from the Taylor coefficients of `f` at `0`.
  -- Step 4.1: Name the Taylor coefficients at the origin in the literal normalized form.
  let c : ℕ → ℂ := fun n => iteratedDeriv n f 0 / (n.factorial : ℂ)

  -- Step 4.2: The polynomial is the finite Taylor sum up to order `N - 1`.
  let p : Polynomial ℂ := ∑ i ∈ Finset.range N, Polynomial.C (c i) * Polynomial.X ^ i

  -- Step 5: Show all Taylor coefficients from order `N` onward vanish.
  -- Step 5.1: First rewrite global vanishing in terms of iterated `deriv`.
  have hN_zero_iterate : deriv^[N] f = (0 : ℂ → ℂ) := by
    simpa [← iteratedDeriv_eq_iterate] using hN_zero_fun

  -- Step 5.2: If `m ≥ N`, write `m = N + k` and differentiate the zero `N`-th
  -- derivative `k` more times.
  have hcoeff_tail : ∀ m : ℕ, N ≤ m → c m = 0 := by
    intro m hm
    obtain ⟨k, rfl⟩ := exists_add_of_le hm
    have hderiv_zero : iteratedDeriv (N + k) f 0 = 0 := by
      rw [Nat.add_comm N k, iteratedDeriv_eq_iterate]
      rw [Function.iterate_add_apply]
      rw [hN_zero_iterate]
      simp [← iteratedDeriv_eq_iterate]
    simp [c, hderiv_zero]

  -- Step 6: Use the analytic Taylor expansion at `0` and the tail vanishing to get
  -- local equality with the finite polynomial `p`.
  -- Step 6.1: The Taylor series of an analytic function has coefficients
  -- `iteratedDeriv n f 0 / n!`.
  have hf_power :
      HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ c) 0 := by
    simpa [c] using (hf_diff.analyticAt 0).hasFPowerSeriesAt

  -- Step 6.2: Choose a ball on which this power series represents `f`.
  rcases hf_power with ⟨r, hr⟩

  -- Step 6.3: Upgrade the power series to a finite power series using the coefficient tail.
  have hf_finite :
      HasFiniteFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ c) 0 N r :=
    { hr with
      finite := by
        intro m hm
        simp [hcoeff_tail m hm] }

  -- Step 6.4: On that ball, the finite power series is exactly the polynomial `p`.
  have hf_eq_poly_near :
      f =ᶠ[𝓝 (0 : ℂ)] fun z : ℂ => Polynomial.aeval (R := ℂ) (A := ℂ) z p := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr ?_
    refine ⟨Metric.eball (0 : ℂ) r, Metric.eball_mem_nhds _ hr.r_pos, ?_⟩
    intro z hz
    have hpartial := hf_finite.eq_partialSum' z hz N le_rfl
    rw [hpartial]
    simp [p, FormalMultilinearSeries.partialSum, FormalMultilinearSeries.ofScalars]

  -- Step 7: Extend the local equality to global equality by the analytic identity theorem.
  -- Step 7.1: The polynomial function is analytic on the whole complex plane.
  have hp_analytic :
      AnalyticOnNhd ℂ (fun z : ℂ => Polynomial.aeval (R := ℂ) (A := ℂ) z p) Set.univ := by
    simpa using
      ((analyticOnNhd_id : AnalyticOnNhd ℂ (fun z : ℂ => z) Set.univ).aeval_polynomial
        (A := ℂ) p)

  -- Step 7.2: Since both functions are entire and agree near `0`, they agree everywhere.
  have hglobal : f = fun z : ℂ => Polynomial.aeval (R := ℂ) (A := ℂ) z p :=
    hf_analytic.eq_of_eventuallyEq hp_analytic hf_eq_poly_near

  -- Step 8: Package the polynomial witness.
  exact ⟨p, by simpa using hglobal⟩

end
