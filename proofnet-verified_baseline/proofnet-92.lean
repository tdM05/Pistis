import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

Prove that $\cos 1^{\circ}$  is algebraic over $\mathbb{Q}$.
-/

/-Informal Proof

Since $\left(\cos \left(1^{\circ}\right)+i \sin \left(1^{\circ}\right)\right)^{360}=1$, the number $\cos \left(1^{\circ}\right)+i \sin \left(1^{\circ}\right)$ is algebraic. And the real part and the imaginary part of an algebraic number are always algebraic numbers.
-/

set_option maxRecDepth 2048 in
theorem Herstein_exercise_5_3_10 : IsAlgebraic ℚ (cos (Real.pi / 180)) := by
  /- Step 1: Fix the angle θ := π / 180 (one degree). -/
  set θ : ℝ := Real.pi / 180 with hθ_def

  /- Step 2: Define the complex number z = exp (θ·i) = cos θ + i·sin θ. -/
  let z : ℂ := Complex.exp (θ * Complex.I)

  /- Step 3: Show z^360 = 1, i.e. z is a 360‑th root of unity. -/
  have hz_pow : z ^ 360 = 1 := by
    -- Step 3.1: rewrite z in the cis form using Euler's formula.
    have hz_def : z = Complex.cos θ + Complex.sin θ * Complex.I := by
      simp [z, Complex.exp_mul_I]
    -- Step 3.2: apply De Moivre's formula to compute the 360‑th power.
    calc
      z ^ 360
          = (Complex.cos θ + Complex.sin θ * Complex.I) ^ 360 := by simp [hz_def]
      _ = Complex.cos ((360 : ℂ) * θ) + Complex.sin ((360 : ℂ) * θ) * Complex.I := by
            -- De Moivre: (cos x + i sin x)^n = cos (n x) + i sin (n x)
            simpa using Complex.cos_add_sin_mul_I_pow 360 (θ : ℂ)
      _ = Complex.cos (2 * Real.pi) + Complex.sin (2 * Real.pi) * Complex.I := by
            -- Step 3.2.1: simplify (360)·θ = 2π.
            -- First prove the identity over ℝ, then cast to ℂ.
            have hangle_real : (360 : ℝ) * θ = 2 * Real.pi := by
              field_simp [hθ_def] ; ring
            have hangle : (360 : ℂ) * (θ : ℂ) = (2 : ℂ) * Real.pi :=
              by exact_mod_cast hangle_real
            simp [hangle]
      _ = 1 := by
            -- Step 3.3: sin (2π)=0 and cos (2π)=1 in ℂ.
            simp [Complex.cos_two_pi, Complex.sin_two_pi]

  /- Step 4: Exhibit a rational-coefficient polynomial that z satisfies:
     p(X) = X^360 - 1. -/
  let p : Polynomial ℚ := (Polynomial.X ^ 360) - 1
  -- Step 4.1: p is nonzero because its leading coefficient is 1.
  have hp_nonzero : p ≠ 0 := by
    -- Use the general lemma X^n - C a ≠ 0 when n>0.
    show (X : ℚ[X]) ^ 360 - 1 ≠ 0
    exact X_pow_sub_C_ne_zero (by norm_num : 0 < 360) 1
  -- Step 4.2: z is a root of p, since z^360 = 1.
  have hp_root : aeval z p = 0 := by
    -- aeval distributes over subtraction; aeval X^n = z^n.
    simp [p, hz_pow]
  -- Step 4.3: conclude z is algebraic over ℚ.
  have hz_alg : IsAlgebraic ℚ z := ⟨p, hp_nonzero, hp_root⟩

  /- Step 5: Express cos θ as a ℚ-linear expression in z and z⁻¹
     and use closure of algebraic numbers under field operations. -/
  -- Step 5.1: also consider the exponential at the negative angle.
  let z_neg : ℂ := Complex.exp (-θ * Complex.I)
  -- Step 5.2: show z_neg is also a 360‑th root of unity.
  have hz_neg_pow : z_neg ^ 360 = 1 := by
    have hz_neg_def : z_neg = Complex.cos (-θ) + Complex.sin (-θ) * Complex.I := by
      simp [z_neg, Complex.exp_mul_I]
    calc
      z_neg ^ 360
          = (Complex.cos (-θ) + Complex.sin (-θ) * Complex.I) ^ 360 := by simp [hz_neg_def]
      _ = Complex.cos ((360 : ℂ) * (-θ)) + Complex.sin ((360 : ℂ) * (-θ)) * Complex.I := by
            simpa using Complex.cos_add_sin_mul_I_pow 360 ((-θ) : ℂ)
      _ = Complex.cos (-2 * Real.pi) + Complex.sin (-2 * Real.pi) * Complex.I := by
            -- (360) * (-θ) = -2π using the earlier identity.
            have hangle_real : (360 : ℝ) * θ = 2 * Real.pi := by
              field_simp [hθ_def] ; ring
            have hangle_real_neg : (360 : ℝ) * (-θ) = -2 * Real.pi := by
              nlinarith
            have hangle_neg : (360 : ℂ) * (-θ) = (-2 : ℂ) * Real.pi :=
              by exact_mod_cast hangle_real_neg
            simp [hangle_neg]
      _ = 1 := by
            -- cos(-2π)=1 and sin(-2π)=0 by parity.
            simp [Complex.cos_neg, Complex.sin_neg, Complex.cos_two_pi, Complex.sin_two_pi]
  -- Step 5.3: both z and z_neg are algebraic (same polynomial X^360 − 1).
  have hz_neg_alg : IsAlgebraic ℚ z_neg := by
    refine ⟨p, hp_nonzero, ?_⟩
    -- hangle from Step 4 shows p has root z_neg.
    have hz_neg_root : aeval z_neg p = 0 := by
      -- evaluate p(z_neg) = z_neg^360 - 1
      simp [p, hz_neg_pow]
    simpa using hz_neg_root
  -- Step 5.4: rewrite Complex.cos θ using z and z_neg.
  have hcos_as : Complex.cos θ = (z + z_neg) / 2 := by
    -- Directly expand the definition of complex cosine.
    simp [Complex.cos, z, z_neg, div_eq_mul_inv]
  -- Step 5.5: the sum z + z_neg is algebraic.
  have hsum_alg : IsAlgebraic ℚ (z + z_neg) := hz_alg.add hz_neg_alg
  -- Step 5.6: multiply by the rational scalar 1/2 to match the cosine formula.
  have hcosC_alg : IsAlgebraic ℚ (Complex.cos θ) := by
    -- Convert the division by 2 into scalar multiplication by 1/2 over ℚ.
    have hscalar :
        (z + z_neg) / 2 = ( (1 / 2 : ℚ) • (z + z_neg) ) := by
          -- Scalar multiplication over ℚ is multiplication by (1/2) inside ℂ.
          calc
            (z + z_neg) / 2
                = (z + z_neg) * ((2 : ℂ)⁻¹) := by simp [div_eq_mul_inv]
            _ = ((2 : ℂ)⁻¹) * (z + z_neg) := by simp [mul_comm]
            _ = (1 / 2 : ℂ) * (z + z_neg) := by norm_num
            _ = (1 / 2 : ℚ) • (z + z_neg) := by simp [Algebra.smul_def]
    -- Replace cos θ with the scalar multiple and apply algebraicity closure.
    simpa [hcos_as, hscalar] using hsum_alg.smul (1 / 2 : ℚ)

  /- Step 6: Transfer algebraicity from ℂ back to ℝ using the embedding ℝ → ℂ. -/
  -- Step 6.1: unpack the witnessing polynomial for the complex cosine.
  obtain ⟨q, hq_nonzero, hq_root⟩ := hcosC_alg
  -- Step 6.2: use functoriality of `aeval` along the embedding `Complex.ofReal`.
  have hcompat :
      (algebraMap ℚ ℂ).comp (RingHom.id ℚ)
        = (Complex.ofRealHom).comp (algebraMap ℚ ℝ) := by
        ext r; rfl
  have hmap :=
    map_aeval_eq_aeval_map (R := ℚ) (S := ℝ) (T := ℚ) (U := ℂ)
      (φ := RingHom.id ℚ) (ψ := Complex.ofRealHom) hcompat q (cos θ)
  -- Simplify the mapped equality: `p.map id = p`.
  have hmap' : Complex.ofReal (aeval (cos θ) q) = aeval (Complex.ofReal (cos θ)) q := by
    simpa using hmap
  -- Step 6.3: identify `Complex.ofReal (cos θ)` with `Complex.cos θ`.
  have hcof_eq : (Complex.ofReal (cos θ)) = Complex.cos θ := by
    -- norm_cast lemma for cosine
    simp [hθ_def]
  -- Step 6.4: the polynomial also annihilates `cos θ` in ℂ.
  have hroot_in_C : aeval (Complex.ofReal (cos θ)) q = 0 := by
    simpa [hcof_eq] using hq_root
  -- Step 6.5: map back to ℝ using the injectivity of `Complex.ofReal`.
  have hroot_in_R : aeval (cos θ) q = 0 := by
    -- apply injectivity to the mapped equality
    apply (Complex.ofReal_injective)
    simpa [hmap'] using hroot_in_C
  -- Step 6.6: package the polynomial witness to finish.
  exact ⟨q, hq_nonzero, hroot_in_R⟩
