import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

Show that there is an infinite number of integers a such that $f(x) = x^7 + 15x^2 - 30x + a$ is irreducible in $Q[x]$.
-/

/-Informal Proof

Via Eisenstein's criterion and observation that 5 divides 15 and $-30$, it is sufficient to find infinitely many $a$ such that 5 divides $a$, but $5^2=25$ doesn't divide $a$. For example $5 \cdot 2^k$ for $k=0,1, \ldots$ is one such infinite sequence.
-/

theorem Herstein_exercise_4_6_3 :
  Infinite {a : ℤ | Irreducible (X^7 + 15*X^2 - 30*X + (a : Polynomial ℚ) : Polynomial ℚ)} := by
  -- Step 1: Work in classical logic.
  classical

  -- Step 2: Define a parametrization of integers `a` that satisfy Eisenstein's criterion at prime 5.
  -- We use `a = 5 + 25 * k` for `k : ℕ`, giving 5, 30, 55, 80, ... (all divisible by 5, not by 25).

  -- Step 2.1: Define the parametrization function.
  let g : ℕ → ℤ := fun n => 5 + 25 * n

  -- Step 3: Prove that `g` is injective.
  have hg_inj : Function.Injective g := by
    intro n m h
    -- Step 3.1: From `5 + 25 * n = 5 + 25 * m`, deduce `25 * n = 25 * m`, then `n = m`.
    simp only [g] at h
    have h' : (25 : ℤ) * n = (25 : ℤ) * m := by omega
    have h'' : (n : ℤ) = (m : ℤ) := by omega
    exact Int.ofNat.inj h''

  -- Step 4: Prove that for each `n : ℕ`, the polynomial `X^7 + 15*X^2 - 30*X + g(n)` is irreducible over ℚ.
  have hg_irr : ∀ n : ℕ, Irreducible (X^7 + 15*X^2 - 30*X + ((g n) : Polynomial ℚ) : Polynomial ℚ) := by
    intro n

    -- Step 4.1: Define the integer polynomial `fℤ` using explicit C coefficients.
    -- We write fℤ = C 1 * X^7 + C 0 * X^6 + C 0 * X^5 + C 0 * X^4 + C 0 * X^3 + C 15 * X^2 + C (-30) * X + C a.
    set a : ℤ := g n with ha_def
    -- Step 4.1.1: Define the polynomial in standard form.
    set fℤ : Polynomial ℤ := X^7 + C 15 * X^2 + C (-30) * X + C a with hfZ_def
    -- Step 4.1.2: Define the prime ideal P = (5).
    set P : Ideal ℤ := Ideal.span {(5 : ℤ)} with hP_def

    -- Step 4.2: Verify that `P` is a proper prime ideal.
    have hPneTop : P ≠ ⊤ := by
      -- Step 4.2.1: 5 is not a unit in ℤ.
      have h5notUnit : ¬ IsUnit (5 : ℤ) := by decide
      -- Step 4.2.2: Hence P is proper.
      simpa [P, Ideal.span_singleton_eq_top] using h5notUnit

    have hPprime : P.IsPrime := by
      -- Step 4.2.3: View 5 as a prime element in ℤ.
      have hPrimeInt : Prime (5 : ℤ) := by
        have hNat : Nat.Prime 5 := by decide
        have hNatAbs : Nat.Prime (Int.natAbs (5 : ℤ)) := by simpa using hNat
        exact (Int.prime_iff_natAbs_prime).2 hNatAbs
      -- Step 4.2.4: Use the principal ideal characterization of primeness.
      have h5ne : (5 : ℤ) ≠ 0 := by decide
      simpa [hP_def] using (Ideal.span_singleton_prime h5ne).2 hPrimeInt

    -- Step 4.3: Show that 5 divides `a` but 25 does not divide `a`.
    have h5_div_a : (5 : ℤ) ∣ a := by
      -- Step 4.3.1: `a = 5 + 25 * n = 5 * (1 + 5 * n)`
      simp only [ha_def, g]
      exact ⟨1 + 5 * n, by ring⟩

    have h25_ndiv_a : ¬ (25 : ℤ) ∣ a := by
      -- Step 4.3.2: `a = 5 + 25 * n`, so `a mod 25 = 5 ≠ 0`.
      simp only [ha_def, g]
      intro ⟨k, hk⟩
      -- Step 4.3.2.1: From `5 + 25 * n = 25 * k`, we get `5 = 25 * (k - n)`.
      have h : (5 : ℤ) = 25 * (k - n) := by omega
      -- Step 4.3.2.2: This means `25 | 5`, contradiction.
      have hdiv : (25 : ℤ) ∣ 5 := ⟨k - n, by omega⟩
      have habs : Int.natAbs 25 ∣ Int.natAbs 5 := Int.natAbs_dvd_natAbs.mpr hdiv
      simp at habs

    -- Step 4.4: Compute the natDegree of `fℤ`.
    have hNatDegree : fℤ.natDegree = 7 := by
      simp only [hfZ_def]
      -- Step 4.4.1: Use the fact that X^7 dominates the other terms.
      have h1 : (X^7 : Polynomial ℤ).natDegree = 7 := natDegree_X_pow 7
      have h2 : (C 15 * X^2 : Polynomial ℤ).natDegree ≤ 2 := by
        calc (C 15 * X^2 : Polynomial ℤ).natDegree
            ≤ (C (15 : ℤ)).natDegree + (X^2 : Polynomial ℤ).natDegree := natDegree_mul_le
          _ = 0 + 2 := by simp
          _ = 2 := by ring
      have h3 : (C (-30) * X : Polynomial ℤ).natDegree ≤ 1 := by
        calc (C (-30) * X : Polynomial ℤ).natDegree
            ≤ (C (-30 : ℤ)).natDegree + (X : Polynomial ℤ).natDegree := natDegree_mul_le
          _ = 0 + 1 := by simp
          _ = 1 := by ring
      have h4 : (C a).natDegree = 0 := natDegree_C a
      -- Step 4.4.2: Combine degree bounds.
      have h5 : (X^7 + C 15 * X^2 : Polynomial ℤ).natDegree = 7 := by
        rw [natDegree_add_eq_left_of_natDegree_lt]
        · exact h1
        · omega
      have h6 : ((X^7 + C 15 * X^2) + C (-30) * X : Polynomial ℤ).natDegree = 7 := by
        rw [natDegree_add_eq_left_of_natDegree_lt]
        · exact h5
        · omega
      have h7 : (((X^7 + C 15 * X^2) + C (-30) * X) + C a : Polynomial ℤ).natDegree = 7 := by
        rw [natDegree_add_eq_left_of_natDegree_lt]
        · exact h6
        · rw [h4]; omega
      convert h7 using 1

    -- Step 4.5: Show that `fℤ` is monic.
    have hMonic : fℤ.Monic := by
      rw [Monic, Polynomial.leadingCoeff, hNatDegree, hfZ_def]
      -- Step 4.5.1: Compute the coefficient at degree 7.
      simp only [coeff_add, coeff_X_pow, coeff_C_mul, coeff_C]
      -- Step 4.5.2: All coefficients except X^7 vanish at degree 7.
      simp [coeff_X]

    -- Step 4.6: Hence `fℤ` is primitive.
    have hfZPrim : fℤ.IsPrimitive := hMonic.isPrimitive

    -- Step 4.7: Record the explicit coefficients.
    have hCoeff0 : fℤ.coeff 0 = a := by
      simp only [hfZ_def, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X]
      simp
    have hCoeff1 : fℤ.coeff 1 = -30 := by
      simp only [hfZ_def, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X]
      simp
    have hCoeff2 : fℤ.coeff 2 = 15 := by
      simp only [hfZ_def, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X]
      simp
    have hCoeff3 : fℤ.coeff 3 = 0 := by
      simp only [hfZ_def, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X]
      simp
    have hCoeff4 : fℤ.coeff 4 = 0 := by
      simp only [hfZ_def, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X]
      simp
    have hCoeff5 : fℤ.coeff 5 = 0 := by
      simp only [hfZ_def, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X]
      simp
    have hCoeff6 : fℤ.coeff 6 = 0 := by
      simp only [hfZ_def, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X]
      simp

    -- Step 4.8: Verify that every lower-degree coefficient lies in the ideal P = (5).
    have hMem : ∀ ⦃m : ℕ⦄, m < fℤ.natDegree → fℤ.coeff m ∈ P := by
      intro m hm
      have hmlt7 : m < 7 := by simpa [hNatDegree] using hm
      -- Step 4.8.1: Case split on m = 0, 1, 2, 3, 4, 5, 6.
      interval_cases m
      · -- Case m = 0: coefficient is `a`, divisible by 5.
        have hDiv : (5 : ℤ) ∣ a := h5_div_a
        simpa [hCoeff0, P] using Ideal.mem_span_singleton.mpr hDiv
      · -- Case m = 1: coefficient is -30, divisible by 5.
        have hDiv : (5 : ℤ) ∣ (-30 : ℤ) := ⟨-6, by norm_num⟩
        simpa [hCoeff1, P] using Ideal.mem_span_singleton.mpr hDiv
      · -- Case m = 2: coefficient is 15, divisible by 5.
        have hDiv : (5 : ℤ) ∣ (15 : ℤ) := ⟨3, by norm_num⟩
        simpa [hCoeff2, P] using Ideal.mem_span_singleton.mpr hDiv
      · -- Case m = 3: coefficient is 0, in every ideal.
        simp [hCoeff3]
      · -- Case m = 4: coefficient is 0.
        simp [hCoeff4]
      · -- Case m = 5: coefficient is 0.
        simp [hCoeff5]
      · -- Case m = 6: coefficient is 0.
        simp [hCoeff6]

    -- Step 4.9: The constant coefficient is not in P^2 = (25).
    have hCoeff0Not : fℤ.coeff 0 ∉ P ^ 2 := by
      -- Step 4.9.1: Assume for contradiction that a ∈ P^2.
      intro hMem
      -- Step 4.9.2: Rewrite P^2 as span {25}.
      have hP2 : P ^ 2 = Ideal.span {(25 : ℤ)} := by
        simp only [hP_def]
        rw [Ideal.span_singleton_pow]
        norm_num
      -- Step 4.9.3: Membership in span {25} means divisibility by 25.
      have hdiv : (25 : ℤ) ∣ a := by
        have hMem' : a ∈ Ideal.span {(25 : ℤ)} := by simpa [hCoeff0, hP2] using hMem
        exact (Ideal.mem_span_singleton).mp hMem'
      -- Step 4.9.4: Contradiction with h25_ndiv_a.
      exact h25_ndiv_a hdiv

    -- Step 4.10: The leading coefficient is not in P (since 1 is not divisible by 5).
    have hLeadNotMem : fℤ.leadingCoeff ∉ P := by
      -- Step 4.10.1: 5 does not divide 1.
      have hNoDiv : ¬ (5 : ℤ) ∣ (1 : ℤ) := by decide
      -- Step 4.10.2: Translate to ideal membership.
      intro hMem
      have hDiv : (5 : ℤ) ∣ fℤ.leadingCoeff := Ideal.mem_span_singleton.mp hMem
      simp [hMonic.leadingCoeff] at hDiv

    -- Step 4.11: Assemble the Eisenstein witness.
    have hEisenstein : fℤ.IsEisensteinAt P := by
      exact Monic.isEisensteinAt_of_mem_of_notMem (f := fℤ) hMonic hPneTop
        (fun {m} hm => hMem hm) hCoeff0Not

    -- Step 4.12: Apply Eisenstein's criterion to get irreducibility over ℤ.
    have hIrredZ : Irreducible fℤ :=
      IsEisensteinAt.irreducible hEisenstein hPprime hfZPrim (by simp [hNatDegree])

    -- Step 4.13: Transport irreducibility to ℚ[X] via Gauss's lemma.
    have hIrredQ : Irreducible (fℤ.map (Int.castRingHom ℚ)) :=
      (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hfZPrim).1 hIrredZ

    -- Step 4.14: Show that the mapped polynomial equals the target polynomial.
    have hMap : fℤ.map (Int.castRingHom ℚ) =
        X^7 + 15*X^2 - 30*X + ((g n) : Polynomial ℚ) := by
      simp only [hfZ_def, ha_def]
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
      -- Step 4.14.1: Simplify the integer cast to rational.
      -- Step 4.14.2: The coercion (g n : Polynomial ℚ) means C ((g n) : ℚ).
      -- We need to show: X^7 + C ↑15 * X^2 + C ↑(-30) * X + C ↑(g n) = X^7 + 15*X^2 - 30*X + ↑(g n)
      -- First, note that 15 * X^2 = C 15 * X^2 and 30 * X = C 30 * X.
      -- Also (g n : Polynomial ℚ) = C ((g n) : ℚ).
      have h1 : (15 : Polynomial ℚ) = C (15 : ℚ) := rfl
      have h2 : (30 : Polynomial ℚ) = C (30 : ℚ) := rfl
      have h3 : ((g n) : Polynomial ℚ) = C ((g n) : ℚ) := rfl
      rw [h1, h2, h3]
      -- Now we have: C ↑15 * X^2 + C ↑(-30) * X + C ↑(g n) = C 15 * X^2 - C 30 * X + C ↑(g n)
      -- The cast of -30 to ℚ equals -30.
      have hcast15 : (Int.castRingHom ℚ) 15 = (15 : ℚ) := by norm_num
      have hcast30 : (Int.castRingHom ℚ) (-30) = (-30 : ℚ) := by norm_num
      have hcastgn : (Int.castRingHom ℚ) (g n) = ((g n) : ℚ) := rfl
      simp only [hcast15, hcast30, hcastgn]
      -- Now need to show: X * C (-30) + X^2 * C 15 + X^7 + C ↑(g n) = -(X * C 30) + X^2 * C 15 + X^7 + C ↑(g n)
      -- We have C (-30) = - C 30.
      have hCneg : (C (-30 : ℚ)) = - C (30 : ℚ) := by simp [map_neg]
      rw [hCneg]
      ring

    -- Step 4.15: Conclude.
    simpa [hMap] using hIrredQ

  -- Step 5: Use the injective image lemma to conclude infinitude.
  have hsubset_inf : Set.Infinite {a : ℤ | Irreducible (X^7 + 15*X^2 - 30*X + (a : Polynomial ℚ) : Polynomial ℚ)} := by
    -- Step 5.1: Every `g n` lies in the solution set.
    have hg_mem : ∀ n : ℕ, g n ∈ {a : ℤ | Irreducible (X^7 + 15*X^2 - 30*X + (a : Polynomial ℚ) : Polynomial ℚ)} := by
      intro n
      simp only [Set.mem_setOf_eq]
      exact hg_irr n
    -- Step 5.2: Apply the infinite injection lemma.
    exact Set.infinite_of_injective_forall_mem hg_inj hg_mem

  -- Step 6: Convert set-level infinitude to subtype infinitude.
  exact (Set.infinite_coe_iff).mpr hsubset_inf
