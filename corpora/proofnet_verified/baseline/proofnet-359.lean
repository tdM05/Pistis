import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset Set
open scoped BigOperators


/-Informal Statement

Suppose $f$ is a real, three times differentiable function on $[-1,1]$, such that $f(-1)=0, \quad f(0)=0, \quad f(1)=1, \quad f^{\prime}(0)=0 .$ Prove that $f^{(3)}(x) \geq 3$ for some $x \in(-1,1)$.
-/

/-Informal Proof

Following the hint, we observe that Theorem $5.15$ (Taylor's formula with remainder) implies that
$$
\begin{aligned}
f(1) &=f(0)+f^{\prime}(0)+\frac{1}{2} f^{\prime \prime}(0)+\frac{1}{6} f^{(3)}(s) \\
f(-1) &=f(0)-f^{\prime}(0)+\frac{1}{2} f^{\prime \prime}(0)-\frac{1}{6} f^{(3)}(t)
\end{aligned}
$$
for some $s \in(0,1), t \in(-1,0)$. By subtracting the second equation from the first and using the given values of $f(1), f(-1)$, and $f^{\prime}(0)$, we obtain
$$
1=\frac{1}{6}\left(f^{(3)}(s)+f^{(3)}(t)\right),
$$
which is the desired result. Note that we made no use of the hypothesis $f(0)=0$.
-/


/-!
## Proof Strategy

This proof uses Taylor's theorem with Lagrange remainder. The key insight is:
- From Taylor's theorem at x = 1: f(1) = f(0) + f'(0) + f''(0)/2 + f'''(s)/6 for some s ∈ (0,1)
- From Taylor's theorem at x = -1: f(-1) = f(0) - f'(0) + f''(0)/2 - f'''(t)/6 for some t ∈ (-1,0)
- Substituting the given values and subtracting: 1 = (f'''(s) + f'''(t))/6
- Therefore f'''(s) + f'''(t) = 6, so max(f'''(s), f'''(t)) ≥ 3

The formalization uses proof by contradiction: assuming f'''(x) < 3 for all x ∈ (-1,1)
leads to contradictory bounds on f''(0).
-/

theorem Rudin_exercise_5_17
  {f : ℝ → ℝ}
  (hf' : DifferentiableOn ℝ f (Icc (-1) 1))
  (hf'' : DifferentiableOn ℝ (deriv f) (Icc (-1) 1))
  (hf''' : DifferentiableOn ℝ (deriv (deriv f)) (Icc (-1) 1))
  (hf0 : f (-1) = 0)
  (hf1 : f 0 = 0)
  (hf2 : f 1 = 1)
  (hf3 : deriv f 0 = 0) :
  ∃ x, x ∈ Ioo (-1 : ℝ) 1 ∧ deriv (deriv (deriv f)) x ≥ 3 := by
  -- =============================================================================
  -- PROOF USING AUXILIARY FUNCTION AND ROLLE'S THEOREM APPLIED THREE TIMES
  --
  -- Step 1: Define a = f''(0) for convenience
  -- Step 2: Define auxiliary function φ(x) = f(x) - (a/2)x² - (1 - a/2)x³
  --         Key properties: φ(0) = 0, φ(1) = 0, φ'(0) = 0, φ''(0) = 0
  -- Step 3: Apply Rolle's theorem three times to get s ∈ (0, 1) with φ'''(s) = 0
  --         This gives f'''(s) = 6 - 3a
  -- Step 4: Similarly for ψ(x) on [-1, 0], get t ∈ (-1, 0) with f'''(t) = 3a
  -- Step 5: f'''(s) + f'''(t) = 6, so max ≥ 3
  -- =============================================================================

  -- Step 1: Set a = f''(0) for convenience
  set a := deriv (deriv f) 0 with ha_def

  -- Step 1.1: Establish continuity properties needed for Rolle's theorem
  have hf_cont : ContinuousOn f (Icc (-1) 1) := hf'.continuousOn
  have hf'_cont : ContinuousOn (deriv f) (Icc (-1) 1) := hf''.continuousOn
  have hf''_cont : ContinuousOn (deriv (deriv f)) (Icc (-1) 1) := hf'''.continuousOn

  -- Step 2: We prove by contradiction - assume f'''(x) < 3 for all x ∈ (-1, 1)
  by_contra h
  push_neg at h

  -- Step 3: Prove existence of s ∈ (0, 1) with f'''(s) = 6 - 3a using Rolle's theorem
  have h_taylor_s : ∃ s ∈ Ioo (0 : ℝ) 1, deriv (deriv (deriv f)) s = 6 - 3 * a := by
    -- Step 3.1: Define auxiliary function φ(x) = f(x) - (a/2)·x² - (1 - a/2)·x³
    let φ := fun x => f x - a / 2 * x ^ 2 - (1 - a / 2) * x ^ 3

    -- Step 3.2: Verify φ(0) = 0
    -- φ(0) = f(0) - (a/2)*0² - (1 - a/2)*0³ = f(0) = 0
    have hφ0 : φ 0 = 0 := by
      show f 0 - a / 2 * 0 ^ 2 - (1 - a / 2) * 0 ^ 3 = 0
      simp [hf1]

    -- Step 3.3: Verify φ(1) = 0
    -- φ(1) = f(1) - (a/2)*1² - (1 - a/2)*1³ = 1 - a/2 - (1 - a/2) = 0
    have hφ1 : φ 1 = 0 := by
      show f 1 - a / 2 * 1 ^ 2 - (1 - a / 2) * 1 ^ 3 = 0
      simp only [one_pow, mul_one, hf2]
      ring

    -- Step 3.4: Establish continuity of φ on [0, 1]
    have hφ_cont : ContinuousOn φ (Icc 0 1) := by
      show ContinuousOn (fun x => f x - a / 2 * x ^ 2 - (1 - a / 2) * x ^ 3) (Icc 0 1)
      apply ContinuousOn.sub
      apply ContinuousOn.sub
      · exact hf_cont.mono (by intro x hx; exact ⟨by linarith [hx.1], hx.2⟩)
      · apply ContinuousOn.mul continuousOn_const
        exact (continuous_pow 2).continuousOn
      · apply ContinuousOn.mul continuousOn_const
        exact (continuous_pow 3).continuousOn

    -- Step 3.5: Apply Rolle's theorem to φ on [0, 1]: ∃ p₁ ∈ (0, 1) with φ'(p₁) = 0
    have h_rolle1 : ∃ p₁ ∈ Ioo (0 : ℝ) 1, deriv φ p₁ = 0 := by
      apply exists_deriv_eq_zero (by norm_num : (0 : ℝ) < 1) hφ_cont
      rw [hφ0, hφ1]

    obtain ⟨p₁, hp₁_mem, hp₁_eq⟩ := h_rolle1

    -- Step 3.6: Define φ' (the derivative of φ)
    let φ' := fun x => deriv f x - a * x - 3 * (1 - a / 2) * x ^ 2

    -- Step 3.7: Verify φ'(0) = 0
    -- φ'(0) = f'(0) - a*0 - 3*(1 - a/2)*0² = 0
    have hφ'0 : φ' 0 = 0 := by
      show deriv f 0 - a * 0 - 3 * (1 - a / 2) * 0 ^ 2 = 0
      simp [hf3]

    -- Step 3.8: Show deriv φ = φ' at p₁
    have hf_diff_p₁ : DifferentiableAt ℝ f p₁ := by
      exact hf'.differentiableAt (Icc_mem_nhds (by linarith [hp₁_mem.1]) hp₁_mem.2)

    have hderiv_φ_p₁ : deriv φ p₁ = φ' p₁ := by
      -- Step 3.8.1: The derivative of φ at p₁ equals φ'(p₁) by direct calculation
      -- φ(x) = f(x) - (a/2)*x² - (1 - a/2)*x³
      -- φ'(x) = f'(x) - a*x - 3*(1 - a/2)*x²
      have hf_at : DifferentiableAt ℝ f p₁ := hf_diff_p₁
      have hp2 : DifferentiableAt ℝ (fun x => x ^ 2) p₁ := differentiableAt_pow 2
      have hp3 : DifferentiableAt ℝ (fun x => x ^ 3) p₁ := differentiableAt_pow 3
      have h2 : DifferentiableAt ℝ (fun x => a / 2 * x ^ 2) p₁ := hp2.const_mul (a / 2)
      have h3 : DifferentiableAt ℝ (fun x => (1 - a / 2) * x ^ 3) p₁ := hp3.const_mul (1 - a / 2)
      -- Step 3.8.2: Use HasDerivAt to compute the derivative
      have hd_f : HasDerivAt f (deriv f p₁) p₁ := hf_at.hasDerivAt
      have hd_2 : HasDerivAt (fun x => a / 2 * x ^ 2) (a / 2 * (2 * p₁ ^ 1)) p₁ :=
        (hasDerivAt_pow 2 p₁).const_mul (a / 2)
      have hd_3 : HasDerivAt (fun x => (1 - a / 2) * x ^ 3) ((1 - a / 2) * (3 * p₁ ^ 2)) p₁ :=
        (hasDerivAt_pow 3 p₁).const_mul (1 - a / 2)
      have hd_φ : HasDerivAt φ (deriv f p₁ - a / 2 * (2 * p₁ ^ 1) - (1 - a / 2) * (3 * p₁ ^ 2)) p₁ :=
        (hd_f.sub hd_2).sub hd_3
      rw [hd_φ.deriv]
      simp only [pow_one]
      ring

    have hφ'p₁ : φ' p₁ = 0 := by rw [← hderiv_φ_p₁, hp₁_eq]

    -- Step 3.9: Establish continuity of φ' on [0, p₁]
    have hφ'_cont : ContinuousOn φ' (Icc 0 p₁) := by
      show ContinuousOn (fun x => deriv f x - a * x - 3 * (1 - a / 2) * x ^ 2) (Icc 0 p₁)
      apply ContinuousOn.sub
      apply ContinuousOn.sub
      · exact hf'_cont.mono (by intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2, hp₁_mem.2]⟩)
      · apply ContinuousOn.mul continuousOn_const continuous_id.continuousOn
      · apply ContinuousOn.mul continuousOn_const (continuous_pow 2).continuousOn

    -- Step 3.10: Apply Rolle's theorem to φ' on [0, p₁]
    have h_rolle2 : ∃ q₁ ∈ Ioo (0 : ℝ) p₁, deriv φ' q₁ = 0 := by
      apply exists_deriv_eq_zero hp₁_mem.1 hφ'_cont
      rw [hφ'0, hφ'p₁]

    obtain ⟨q₁, hq₁_mem, hq₁_eq⟩ := h_rolle2

    -- Step 3.11: Define φ'' (the second derivative of φ)
    let φ'' := fun x => deriv (deriv f) x - a - 6 * (1 - a / 2) * x

    -- Step 3.12: Verify φ''(0) = 0
    -- φ''(0) = f''(0) - a - 6*(1 - a/2)*0 = a - a = 0
    have hφ''0 : φ'' 0 = 0 := by
      show deriv (deriv f) 0 - a - 6 * (1 - a / 2) * 0 = 0
      simp [ha_def]

    -- Step 3.13: Show deriv φ' = φ'' at q₁
    have hf'_diff_q₁ : DifferentiableAt ℝ (deriv f) q₁ := by
      exact hf''.differentiableAt (Icc_mem_nhds (by linarith [hq₁_mem.1]) (by linarith [hq₁_mem.2, hp₁_mem.2]))

    have hderiv_φ'_q₁ : deriv φ' q₁ = φ'' q₁ := by
      -- Step 3.13.1: The derivative of φ' at q₁ equals φ''(q₁) by direct calculation
      -- φ'(x) = f'(x) - a*x - 3*(1 - a/2)*x²
      -- φ''(x) = f''(x) - a - 6*(1 - a/2)*x
      have h1 : DifferentiableAt ℝ (deriv f) q₁ := hf'_diff_q₁
      have hid : DifferentiableAt ℝ id q₁ := differentiableAt_id
      have hp2 : DifferentiableAt ℝ (fun x => x ^ 2) q₁ := differentiableAt_pow 2
      have h2 : DifferentiableAt ℝ (fun x => a * x) q₁ := hid.const_mul a
      have h3 : DifferentiableAt ℝ (fun x => 3 * (1 - a / 2) * x ^ 2) q₁ := hp2.const_mul (3 * (1 - a / 2))
      -- Step 3.13.2: Use HasDerivAt to compute the derivative
      have hd_1 : HasDerivAt (deriv f) (deriv (deriv f) q₁) q₁ := h1.hasDerivAt
      have hd_2 : HasDerivAt (fun x => a * x) (a * 1) q₁ := (hasDerivAt_id q₁).const_mul a
      have hd_3 : HasDerivAt (fun x => 3 * (1 - a / 2) * x ^ 2) (3 * (1 - a / 2) * (2 * q₁ ^ 1)) q₁ :=
        (hasDerivAt_pow 2 q₁).const_mul (3 * (1 - a / 2))
      have hd_φ' : HasDerivAt φ' (deriv (deriv f) q₁ - a * 1 - 3 * (1 - a / 2) * (2 * q₁ ^ 1)) q₁ :=
        (hd_1.sub hd_2).sub hd_3
      rw [hd_φ'.deriv]
      simp only [pow_one, mul_one]
      ring

    have hφ''q₁ : φ'' q₁ = 0 := by rw [← hderiv_φ'_q₁, hq₁_eq]

    -- Step 3.14: Establish continuity of φ'' on [0, q₁]
    have hφ''_cont : ContinuousOn φ'' (Icc 0 q₁) := by
      show ContinuousOn (fun x => deriv (deriv f) x - a - 6 * (1 - a / 2) * x) (Icc 0 q₁)
      apply ContinuousOn.sub
      apply ContinuousOn.sub
      · exact hf''_cont.mono (by intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2, hq₁_mem.2, hp₁_mem.2]⟩)
      · exact continuousOn_const
      · apply ContinuousOn.mul continuousOn_const continuous_id.continuousOn

    -- Step 3.15: Apply Rolle's theorem to φ'' on [0, q₁]
    have h_rolle3 : ∃ s ∈ Ioo (0 : ℝ) q₁, deriv φ'' s = 0 := by
      apply exists_deriv_eq_zero hq₁_mem.1 hφ''_cont
      rw [hφ''0, hφ''q₁]

    obtain ⟨s, hs_mem, hs_eq⟩ := h_rolle3

    -- Step 3.16: Show deriv φ'' s = f'''(s) - 6*(1 - a/2)
    have hf''_diff_s : DifferentiableAt ℝ (deriv (deriv f)) s := by
      exact hf'''.differentiableAt (Icc_mem_nhds (by linarith [hs_mem.1]) (by linarith [hs_mem.2, hq₁_mem.2, hp₁_mem.2]))

    have hderiv_φ''_s : deriv φ'' s = deriv (deriv (deriv f)) s - 6 * (1 - a / 2) := by
      -- Step 3.16.1: The derivative of φ'' at s equals f'''(s) - 6*(1 - a/2)
      -- φ''(x) = f''(x) - a - 6*(1 - a/2)*x
      -- φ'''(x) = f'''(x) - 6*(1 - a/2)
      have h1 : DifferentiableAt ℝ (deriv (deriv f)) s := hf''_diff_s
      -- Step 3.16.2: Use HasDerivAt to compute the derivative
      have hd_1 : HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) s) s := h1.hasDerivAt
      have hd_2 : HasDerivAt (fun _ => a) 0 s := hasDerivAt_const s a
      have hd_3 : HasDerivAt (fun x => 6 * (1 - a / 2) * x) (6 * (1 - a / 2) * 1) s :=
        (hasDerivAt_id s).const_mul (6 * (1 - a / 2))
      have hd_φ'' : HasDerivAt φ'' (deriv (deriv (deriv f)) s - 0 - 6 * (1 - a / 2) * 1) s :=
        (hd_1.sub hd_2).sub hd_3
      rw [hd_φ''.deriv]
      ring

    -- Step 3.17: From hs_eq: deriv φ'' s = 0, we get f'''(s) = 6 - 3a
    have hs_result : deriv (deriv (deriv f)) s = 6 - 3 * a := by
      have : deriv (deriv (deriv f)) s - 6 * (1 - a / 2) = 0 := by rw [← hderiv_φ''_s, hs_eq]
      linarith

    -- Step 3.18: Verify s ∈ (0, 1)
    have hs_in_01 : s ∈ Ioo (0 : ℝ) 1 := ⟨hs_mem.1, by linarith [hs_mem.2, hq₁_mem.2, hp₁_mem.2]⟩

    exact ⟨s, hs_in_01, hs_result⟩

  -- Step 4: Prove existence of t ∈ (-1, 0) with f'''(t) = 3a using Rolle's theorem
  have h_taylor_t : ∃ t ∈ Ioo (-1 : ℝ) 0, deriv (deriv (deriv f)) t = 3 * a := by
    -- Step 4.1: Define auxiliary function ψ(x) = f(x) - (a/2)·x² - (a/2)·x³
    let ψ := fun x => f x - a / 2 * x ^ 2 - a / 2 * x ^ 3

    -- Step 4.2: Verify ψ(0) = 0
    -- ψ(0) = f(0) - (a/2)*0² - (a/2)*0³ = f(0) = 0
    have hψ0 : ψ 0 = 0 := by
      show f 0 - a / 2 * 0 ^ 2 - a / 2 * 0 ^ 3 = 0
      simp [hf1]

    -- Step 4.3: Verify ψ(-1) = 0
    -- ψ(-1) = f(-1) - (a/2)*1 - (a/2)*(-1) = 0 - a/2 + a/2 = 0
    have hψm1 : ψ (-1) = 0 := by
      show f (-1) - a / 2 * (-1) ^ 2 - a / 2 * (-1) ^ 3 = 0
      simp [hf0]
      ring

    -- Step 4.4: Establish continuity of ψ on [-1, 0]
    have hψ_cont : ContinuousOn ψ (Icc (-1) 0) := by
      show ContinuousOn (fun x => f x - a / 2 * x ^ 2 - a / 2 * x ^ 3) (Icc (-1) 0)
      apply ContinuousOn.sub
      apply ContinuousOn.sub
      · exact hf_cont.mono (by intro x hx; exact ⟨hx.1, by linarith [hx.2]⟩)
      · apply ContinuousOn.mul continuousOn_const (continuous_pow 2).continuousOn
      · apply ContinuousOn.mul continuousOn_const (continuous_pow 3).continuousOn

    -- Step 4.5: Apply Rolle's theorem to ψ on [-1, 0]
    have h_rolle1' : ∃ p₂ ∈ Ioo (-1 : ℝ) 0, deriv ψ p₂ = 0 := by
      apply exists_deriv_eq_zero (by norm_num : (-1 : ℝ) < 0) hψ_cont
      rw [hψm1, hψ0]

    obtain ⟨p₂, hp₂_mem, hp₂_eq⟩ := h_rolle1'

    -- Step 4.6: Define ψ'
    let ψ' := fun x => deriv f x - a * x - 3 * (a / 2) * x ^ 2

    -- Step 4.7: Verify ψ'(0) = 0
    -- ψ'(0) = f'(0) - a*0 - 3*(a/2)*0² = 0
    have hψ'0 : ψ' 0 = 0 := by
      show deriv f 0 - a * 0 - 3 * (a / 2) * 0 ^ 2 = 0
      simp [hf3]

    -- Step 4.8: Show deriv ψ = ψ' at p₂
    have hf_diff_p₂ : DifferentiableAt ℝ f p₂ := by
      exact hf'.differentiableAt (Icc_mem_nhds hp₂_mem.1 (by linarith [hp₂_mem.2]))

    have hderiv_ψ_p₂ : deriv ψ p₂ = ψ' p₂ := by
      -- Step 4.8.1: The derivative of ψ at p₂ equals ψ'(p₂) by direct calculation
      -- ψ(x) = f(x) - (a/2)*x² - (a/2)*x³
      -- ψ'(x) = f'(x) - a*x - 3*(a/2)*x²
      have hf_at : DifferentiableAt ℝ f p₂ := hf_diff_p₂
      -- Step 4.8.2: Use HasDerivAt to compute the derivative
      have hd_f : HasDerivAt f (deriv f p₂) p₂ := hf_at.hasDerivAt
      have hd_2 : HasDerivAt (fun x => a / 2 * x ^ 2) (a / 2 * (2 * p₂ ^ 1)) p₂ :=
        (hasDerivAt_pow 2 p₂).const_mul (a / 2)
      have hd_3 : HasDerivAt (fun x => a / 2 * x ^ 3) (a / 2 * (3 * p₂ ^ 2)) p₂ :=
        (hasDerivAt_pow 3 p₂).const_mul (a / 2)
      have hd_ψ : HasDerivAt ψ (deriv f p₂ - a / 2 * (2 * p₂ ^ 1) - a / 2 * (3 * p₂ ^ 2)) p₂ :=
        (hd_f.sub hd_2).sub hd_3
      rw [hd_ψ.deriv]
      simp only [pow_one]
      ring

    have hψ'p₂ : ψ' p₂ = 0 := by rw [← hderiv_ψ_p₂, hp₂_eq]

    -- Step 4.9: Establish continuity of ψ' on [p₂, 0]
    have hψ'_cont : ContinuousOn ψ' (Icc p₂ 0) := by
      show ContinuousOn (fun x => deriv f x - a * x - 3 * (a / 2) * x ^ 2) (Icc p₂ 0)
      apply ContinuousOn.sub
      apply ContinuousOn.sub
      · exact hf'_cont.mono (by intro x hx; exact ⟨by linarith [hx.1, hp₂_mem.1], by linarith [hx.2]⟩)
      · apply ContinuousOn.mul continuousOn_const continuous_id.continuousOn
      · apply ContinuousOn.mul continuousOn_const (continuous_pow 2).continuousOn

    -- Step 4.10: Apply Rolle's theorem to ψ' on [p₂, 0]
    have h_rolle2' : ∃ q₂ ∈ Ioo p₂ (0 : ℝ), deriv ψ' q₂ = 0 := by
      apply exists_deriv_eq_zero hp₂_mem.2 hψ'_cont
      rw [hψ'p₂, hψ'0]

    obtain ⟨q₂, hq₂_mem, hq₂_eq⟩ := h_rolle2'

    -- Step 4.11: Define ψ''
    let ψ'' := fun x => deriv (deriv f) x - a - 3 * a * x

    -- Step 4.12: Verify ψ''(0) = 0
    -- ψ''(0) = f''(0) - a - 3*a*0 = a - a = 0
    have hψ''0 : ψ'' 0 = 0 := by
      show deriv (deriv f) 0 - a - 3 * a * 0 = 0
      simp [ha_def]

    -- Step 4.13: Show deriv ψ' = ψ'' at q₂
    have hf'_diff_q₂ : DifferentiableAt ℝ (deriv f) q₂ := by
      exact hf''.differentiableAt (Icc_mem_nhds (by linarith [hq₂_mem.1, hp₂_mem.1]) (by linarith [hq₂_mem.2]))

    have hderiv_ψ'_q₂ : deriv ψ' q₂ = ψ'' q₂ := by
      -- Step 4.13.1: The derivative of ψ' at q₂ equals ψ''(q₂) by direct calculation
      -- ψ'(x) = f'(x) - a*x - 3*(a/2)*x²
      -- ψ''(x) = f''(x) - a - 3*a*x
      have h1 : DifferentiableAt ℝ (deriv f) q₂ := hf'_diff_q₂
      -- Step 4.13.2: Use HasDerivAt to compute the derivative
      have hd_1 : HasDerivAt (deriv f) (deriv (deriv f) q₂) q₂ := h1.hasDerivAt
      have hd_2 : HasDerivAt (fun x => a * x) (a * 1) q₂ := (hasDerivAt_id q₂).const_mul a
      have hd_3 : HasDerivAt (fun x => 3 * (a / 2) * x ^ 2) (3 * (a / 2) * (2 * q₂ ^ 1)) q₂ :=
        (hasDerivAt_pow 2 q₂).const_mul (3 * (a / 2))
      have hd_ψ' : HasDerivAt ψ' (deriv (deriv f) q₂ - a * 1 - 3 * (a / 2) * (2 * q₂ ^ 1)) q₂ :=
        (hd_1.sub hd_2).sub hd_3
      rw [hd_ψ'.deriv]
      simp only [pow_one, mul_one]
      ring

    have hψ''q₂ : ψ'' q₂ = 0 := by rw [← hderiv_ψ'_q₂, hq₂_eq]

    -- Step 4.14: Establish continuity of ψ'' on [q₂, 0]
    have hψ''_cont : ContinuousOn ψ'' (Icc q₂ 0) := by
      show ContinuousOn (fun x => deriv (deriv f) x - a - 3 * a * x) (Icc q₂ 0)
      apply ContinuousOn.sub
      apply ContinuousOn.sub
      · exact hf''_cont.mono (by intro x hx; exact ⟨by linarith [hx.1, hq₂_mem.1, hp₂_mem.1], by linarith [hx.2]⟩)
      · exact continuousOn_const
      · apply ContinuousOn.mul continuousOn_const continuous_id.continuousOn

    -- Step 4.15: Apply Rolle's theorem to ψ'' on [q₂, 0]
    have h_rolle3' : ∃ t ∈ Ioo q₂ (0 : ℝ), deriv ψ'' t = 0 := by
      apply exists_deriv_eq_zero hq₂_mem.2 hψ''_cont
      rw [hψ''q₂, hψ''0]

    obtain ⟨t, ht_mem, ht_eq⟩ := h_rolle3'

    -- Step 4.16: Show deriv ψ'' t = f'''(t) - 3a
    have hf''_diff_t : DifferentiableAt ℝ (deriv (deriv f)) t := by
      exact hf'''.differentiableAt (Icc_mem_nhds (by linarith [ht_mem.1, hq₂_mem.1, hp₂_mem.1]) (by linarith [ht_mem.2]))

    have hderiv_ψ''_t : deriv ψ'' t = deriv (deriv (deriv f)) t - 3 * a := by
      -- Step 4.16.1: The derivative of ψ'' at t equals f'''(t) - 3a
      -- ψ''(x) = f''(x) - a - 3*a*x
      -- ψ'''(x) = f'''(x) - 3*a
      have h1 : DifferentiableAt ℝ (deriv (deriv f)) t := hf''_diff_t
      -- Step 4.16.2: Use HasDerivAt to compute the derivative
      have hd_1 : HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) t) t := h1.hasDerivAt
      have hd_2 : HasDerivAt (fun _ => a) 0 t := hasDerivAt_const t a
      have hd_3 : HasDerivAt (fun x => 3 * a * x) (3 * a * 1) t := (hasDerivAt_id t).const_mul (3 * a)
      have hd_ψ'' : HasDerivAt ψ'' (deriv (deriv (deriv f)) t - 0 - 3 * a * 1) t :=
        (hd_1.sub hd_2).sub hd_3
      rw [hd_ψ''.deriv]
      ring

    -- Step 4.17: From ht_eq, we get f'''(t) = 3a
    have ht_result : deriv (deriv (deriv f)) t = 3 * a := by
      have : deriv (deriv (deriv f)) t - 3 * a = 0 := by rw [← hderiv_ψ''_t, ht_eq]
      linarith

    -- Step 4.18: Verify t ∈ (-1, 0)
    have ht_in_m10 : t ∈ Ioo (-1 : ℝ) 0 := ⟨by linarith [ht_mem.1, hq₂_mem.1, hp₂_mem.1], ht_mem.2⟩

    exact ⟨t, ht_in_m10, ht_result⟩

  -- Step 5: Derive contradiction from the Taylor theorem results
  obtain ⟨s, hs_mem, hs_eq⟩ := h_taylor_s
  obtain ⟨t, ht_mem, ht_eq⟩ := h_taylor_t

  -- Step 5.1: Verify s ∈ (-1, 1)
  have hs_in : s ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hs_mem.1], hs_mem.2⟩

  -- Step 5.2: Verify t ∈ (-1, 1)
  have ht_in : t ∈ Ioo (-1 : ℝ) 1 := ⟨ht_mem.1, by linarith [ht_mem.2]⟩

  -- Step 5.3: Apply hypothesis h to get f'''(s) < 3 and f'''(t) < 3
  have hs_bound : deriv (deriv (deriv f)) s < 3 := h s hs_in
  have ht_bound : deriv (deriv (deriv f)) t < 3 := h t ht_in

  -- Step 5.4: From f'''(s) = 6 - 3a < 3, derive a > 1
  have ha_gt_1 : a > 1 := by linarith [hs_eq.symm ▸ hs_bound]

  -- Step 5.5: From f'''(t) = 3a < 3, derive a < 1
  have ha_lt_1 : a < 1 := by linarith [ht_eq.symm ▸ ht_bound]

  -- Step 5.6: Contradiction: a > 1 and a < 1 is impossible
  linarith
