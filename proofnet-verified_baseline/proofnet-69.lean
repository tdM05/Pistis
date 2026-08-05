import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that $\frac{(x+2)^p-2^p}{x}$, where $p$ is an odd prime, is irreducible in $\mathbb{Z}[x]$.
-/

/-Informal Proof

$\frac{(x+2)^p-2^p}{x} \quad \quad p$ is on add pprime $Z[x]$
$$
\frac{(x+2)^p-2^p}{x} \quad \text { as a polynomial we expand }(x+2)^p
$$
$2^p$ cancels with $-2^p$, every remaining term has $x$ as $a$ factor
$$
\begin{aligned}
& x^{p-1}+2\left(\begin{array}{l}
p \\
1
\end{array}\right) x^{p-2}+2^2\left(\begin{array}{l}
p \\
2
\end{array}\right) x^{p-3}+\ldots+2^{p-1}\left(\begin{array}{c}
p \\
p-1
\end{array}\right) \\
& 2^k\left(\begin{array}{l}
p \\
k
\end{array}\right) x^{p-k-1}=2^k \cdot p \cdot(p-1) \ldots(p-k-1), \quad 0<k<p
\end{aligned}
$$
Every lower order coef. has $p$ as a factor but doesnt have $\$ \mathrm{p}^{\wedge} 2 \$$ as a fuction so the polynomial is irreducible by Eisenstein's Criterion.
-/

theorem Dummit_Foote_exercise_9_4_2d {p : ℕ} (hp : p.Prime ∧ p > 2)
  {f : Polynomial ℤ} (hf : f = (X + 2)^p):
  Irreducible (∑ n ∈ (f.support \ {0}), (f.coeff n : Polynomial ℤ) * X ^ (n-1) :
  Polynomial ℤ) := by
  -- Step 1: Extract the prime conditions from hypothesis
  obtain ⟨hp_prime, hp_gt2⟩ := hp
  -- Step 1.1: Get that p ≥ 1 (needed later)
  have hp_pos : 0 < p := hp_prime.pos
  -- Step 1.2: Get that p ≥ 2
  have hp_ge2 : 2 ≤ p := hp_prime.two_le
  -- Step 1.3: Get that p - 1 < p (needed for hg_coeff)
  have hp_sub1_lt : p - 1 < p := Nat.sub_lt hp_pos (by omega : 0 < 1)

  -- Step 2: Define the polynomial g as the sum we're proving irreducible
  -- This is ((X+2)^p - 2^p) / X
  set g : Polynomial ℤ := ∑ n ∈ (f.support \ {0}), (f.coeff n : Polynomial ℤ) * X ^ (n-1) with hg_def

  -- Step 3: Establish the explicit formula for g
  -- g = ∑_{k=0}^{p-1} C(p, k+1) * 2^{p-k-1} * X^k

  -- Step 4: Define the prime ideal P = (p) ⊂ ℤ
  set P : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ) with hP_def

  -- Step 4.1: Show P is prime
  have hP_prime : P.IsPrime := by
    have hPrimeInt : Prime (p : ℤ) := by
      have hNatAbs : Nat.Prime (Int.natAbs (p : ℤ)) := by simpa using hp_prime
      exact Int.prime_iff_natAbs_prime.2 hNatAbs
    simpa [P] using (Ideal.span_singleton_prime (by omega : (p : ℤ) ≠ 0)).2 hPrimeInt

  -- Step 4.2: Show P ≠ ⊤
  have hP_ne_top : P ≠ ⊤ := by
    have h_not_unit : ¬ IsUnit (p : ℤ) := by
      intro h
      have := Int.isUnit_iff_natAbs_eq.mp h
      simp at this
      omega
    simpa [P, Ideal.span_singleton_eq_top] using h_not_unit

  -- Step 5: Show that f has support exactly {0, 1, ..., p}
  -- Note: We work directly with coefficients using coeff_X_add_C_pow.

  -- Step 5.1: f.coeff k = C(p,k) * 2^{p-k}
  have hf_coeff : ∀ k ≤ p, f.coeff k = (p.choose k : ℤ) * 2^(p - k) := by
    intro k hk
    rw [hf]
    -- Convert 2 to C 2
    have h2_eq : (2 : Polynomial ℤ) = C 2 := by rfl
    rw [h2_eq, coeff_X_add_C_pow]
    -- coeff_X_add_C_pow gives: ((X + C r) ^ n).coeff k = r ^ (n - k) * (n.choose k : R)
    ring

  -- Step 6: Show that the support of f is exactly Finset.range (p + 1)
  -- (We need: for k ≤ p, f.coeff k ≠ 0)
  have hf_coeff_ne_zero : ∀ k ≤ p, f.coeff k ≠ 0 := by
    intro k hk
    rw [hf_coeff k hk]
    apply mul_ne_zero
    · simp only [ne_eq, Int.natCast_eq_zero]
      exact Nat.choose_pos hk |>.ne'
    · exact pow_ne_zero _ (by norm_num)

  -- Step 7: Simplify the polynomial g
  -- g = ∑_{n ∈ f.support \ {0}} f.coeff(n) * X^{n-1}
  --   = ∑_{k=1}^{p} f.coeff(k) * X^{k-1}
  --   = ∑_{j=0}^{p-1} f.coeff(j+1) * X^j
  --   = ∑_{j=0}^{p-1} C(p, j+1) * 2^{p-j-1} * X^j

  -- Step 7.1: Establish that f.support contains exactly {0, 1, ..., p}
  have hf_support : f.support = Finset.range (p + 1) := by
    ext k
    simp only [mem_support_iff, Finset.mem_range]
    constructor
    · intro h
      by_contra h_neg
      push_neg at h_neg
      -- For k ≥ p + 1, f.coeff k = 0 since f = (X + 2)^p has degree p
      have hf_zero : f.coeff k = 0 := by
        rw [hf]
        have h2_eq : (2 : Polynomial ℤ) = C 2 := by rfl
        rw [h2_eq, coeff_X_add_C_pow]
        -- When k > p, n.choose k = 0
        have hchoose : p.choose k = 0 := Nat.choose_eq_zero_of_lt h_neg
        simp [hchoose]
      exact h hf_zero
    · intro hk
      exact hf_coeff_ne_zero k (Nat.lt_succ_iff.mp hk)

  -- Step 7.2: Show support without 0 is {1, ..., p}
  have hf_support_no_zero : f.support \ {0} = Finset.Icc 1 p := by
    ext k
    simp only [Finset.mem_sdiff, Finset.mem_singleton, hf_support, Finset.mem_range, Finset.mem_Icc]
    omega

  -- Step 8: Show that g has a nice closed form
  -- g.coeff j = C(p, j+1) * 2^{p-j-1} for j = 0, ..., p-1
  have hg_coeff : ∀ j < p, g.coeff j = (p.choose (j + 1) : ℤ) * 2^(p - j - 1) := by
    intro j hj
    rw [hg_def]
    rw [finset_sum_coeff]
    rw [hf_support_no_zero]
    -- The sum picks out the term where n - 1 = j, i.e., n = j + 1
    rw [Finset.sum_eq_single (j + 1)]
    · -- Step 8.1: The term n = j + 1 contributes f.coeff(j+1) * 1
      -- Note: (f.coeff n : Polynomial ℤ) = C (f.coeff n), so (C a * X^k).coeff k = a
      -- First convert coercion to C
      rw [show (f.coeff (j+1) : Polynomial ℤ) = C (f.coeff (j+1)) from (C_eq_intCast _).symm]
      rw [coeff_C_mul_X_pow]
      -- Now simplify: if j = (j+1) - 1 then f.coeff (j+1) else 0
      have h_eq : j = (j + 1) - 1 := by omega
      rw [if_pos h_eq]
      rw [hf_coeff (j + 1) (by omega : j + 1 ≤ p)]
      have h_pow_eq : p - (j + 1) = p - j - 1 := by omega
      rw [h_pow_eq]
    · -- Step 8.2: Other terms contribute 0
      intro n hn hn_ne
      simp only [Finset.mem_Icc] at hn
      -- The coeff of X^j in C(f.coeff n) * X^{n-1} is 0 when n ≠ j + 1
      -- First convert coercion to C
      rw [show (f.coeff n : Polynomial ℤ) = C (f.coeff n) from (C_eq_intCast _).symm]
      rw [coeff_C_mul_X_pow]
      -- This equals f.coeff n if j = n - 1, else 0
      split_ifs with h_eq
      · -- If j = n - 1, then n = j + 1, contradiction
        exfalso
        apply hn_ne
        omega
      · -- Otherwise the coefficient is 0
        rfl
    · -- Step 8.3: If j+1 not in range, contradiction
      intro h_not_mem
      simp only [Finset.mem_Icc, not_and, not_le] at h_not_mem
      exfalso
      have hj1_ge1 : 1 ≤ j + 1 := by omega
      have hj1_le_p : j + 1 ≤ p := by omega
      have := h_not_mem hj1_ge1
      omega

  -- Step 9: Show g has degree p - 1
  have hg_degree : g.natDegree = p - 1 := by
    -- The leading coefficient is C(p, p) * 2^0 = 1
    have hg_coeff_leading : g.coeff (p - 1) = 1 := by
      rw [hg_coeff (p - 1) hp_sub1_lt]
      have heq1 : p - 1 + 1 = p := Nat.sub_add_cancel hp_pos
      have heq2 : p - (p - 1) - 1 = 0 := by omega
      simp only [heq1, Nat.choose_self, Nat.cast_one, heq2, pow_zero, mul_one]

    -- First show g has degree ≤ p - 1
    have hg_degree_le : g.natDegree ≤ p - 1 := by
      apply natDegree_le_of_degree_le
      rw [hg_def]
      -- Use degree_sum_le to bound degree by sup
      apply le_trans (Polynomial.degree_sum_le _ _)
      -- Show sup over all terms is ≤ p - 1
      apply Finset.sup_le
      intro n hn
      simp only [Finset.mem_sdiff, Finset.mem_singleton, hf_support, Finset.mem_range] at hn
      have hn_le_p : n ≤ p := by omega
      have hn_pos : 0 < n := by omega
      calc degree (C (f.coeff n) * X ^ (n - 1))
          ≤ (n - 1 : ℕ) := Polynomial.degree_C_mul_X_pow_le (n - 1) _
        _ ≤ (p - 1 : ℕ) := by
            have h : n - 1 ≤ p - 1 := Nat.sub_le_sub_right hn_le_p 1
            exact mod_cast h

    -- Now show degree = p - 1 by showing leading coeff is nonzero
    apply le_antisymm hg_degree_le
    apply Polynomial.le_natDegree_of_ne_zero
    rw [hg_coeff_leading]
    exact one_ne_zero

  -- Step 10: Show g is monic
  have hg_monic : g.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hg_degree]
    rw [hg_coeff (p - 1) hp_sub1_lt]
    have heq1 : p - 1 + 1 = p := Nat.sub_add_cancel hp_pos
    have heq2 : p - (p - 1) - 1 = 0 := by omega
    simp only [heq1, Nat.choose_self, Nat.cast_one, heq2, pow_zero, mul_one]

  -- Step 11: Verify Eisenstein conditions at P
  -- Step 11.1: All non-leading coefficients are in P (divisible by p)
  have hg_lower_coeffs_in_P : ∀ j < g.natDegree, g.coeff j ∈ P := by
    intro j hj
    rw [hg_degree] at hj
    rw [hg_coeff j (by omega : j < p)]
    -- Need to show p | C(p, j+1) * 2^{p-j-1}
    -- Since 1 ≤ j+1 < p, p | C(p, j+1)
    have hj_ne_zero : j + 1 ≠ 0 := by omega
    have hj_bound_hi : j + 1 < p := by omega
    have hp_dvd_choose : (p : ℤ) ∣ (p.choose (j + 1) : ℤ) := by
      -- Use dvd_choose_self: p | C(p, k) for 0 < k < p
      have := hp_prime.dvd_choose_self hj_ne_zero hj_bound_hi
      exact Int.natCast_dvd_natCast.mpr this
    simp only [P, Ideal.mem_span_singleton]
    exact dvd_mul_of_dvd_left hp_dvd_choose _

  -- Step 11.2: Constant coefficient is not in P^2
  have hg_const_not_in_P2 : g.coeff 0 ∉ P ^ 2 := by
    -- g.coeff 0 = C(p, 1) * 2^{p-1} = p * 2^{p-1}
    have hg0 : g.coeff 0 = (p : ℤ) * 2^(p - 1) := by
      rw [hg_coeff 0 hp_pos]
      simp only [zero_add, Nat.choose_one_right]
      have : p - 0 - 1 = p - 1 := by omega
      simp only [this]
    rw [hg0]
    -- Need to show p^2 does not divide p * 2^{p-1}
    intro h_mem
    -- P^2 = span {p^2}
    have hP2_eq : P ^ 2 = Ideal.span ({(p : ℤ) ^ 2} : Set ℤ) := by
      simp only [P, pow_two, Ideal.span_singleton_mul_span_singleton]
    rw [hP2_eq, Ideal.mem_span_singleton] at h_mem
    -- So p^2 | p * 2^{p-1}
    have h_dvd : (p : ℤ) ^ 2 ∣ (p : ℤ) * 2^(p - 1) := h_mem
    -- This means p | 2^{p-1}
    have hp_ne_zero : (p : ℤ) ≠ 0 := by omega
    have h_dvd' : (p : ℤ) ∣ 2^(p - 1) := by
      rw [pow_two] at h_dvd
      exact (mul_dvd_mul_iff_left hp_ne_zero).mp h_dvd
    -- But p > 2 and p is prime, so gcd(p, 2) = 1, hence gcd(p, 2^{p-1}) = 1
    have h_coprime : Nat.Coprime p 2 := by
      apply Nat.Prime.coprime_iff_not_dvd hp_prime |>.mpr
      intro h_dvd_2
      have : p ≤ 2 := Nat.le_of_dvd (by norm_num) h_dvd_2
      omega
    have h_coprime_pow : Nat.Coprime p (2^(p - 1)) := h_coprime.pow_right (p - 1)
    -- p divides 2^{p-1} contradicts coprimality
    have hp_dvd_nat : p ∣ 2^(p - 1) := by
      -- h_dvd' : (p : ℤ) ∣ (2 : ℤ)^(p - 1)
      -- Need to convert to natural divisibility
      -- Use Int.coe_nat_dvd to convert
      have h_pow_nat_eq : (2 : ℤ)^(p - 1) = ((2^(p - 1) : ℕ) : ℤ) := by norm_cast
      rw [h_pow_nat_eq] at h_dvd'
      exact Int.natCast_dvd_natCast.mp h_dvd'
    have : p ∣ Nat.gcd p (2^(p - 1)) := Nat.dvd_gcd (dvd_refl p) hp_dvd_nat
    rw [h_coprime_pow.gcd_eq_one] at this
    exact hp_prime.not_dvd_one this

  -- Step 11.3: Leading coefficient is not in P
  have hg_leading_not_in_P : g.leadingCoeff ∉ P := by
    rw [Polynomial.leadingCoeff, hg_degree, hg_coeff (p - 1) hp_sub1_lt]
    have heq1 : p - 1 + 1 = p := Nat.sub_add_cancel hp_pos
    have heq2 : p - (p - 1) - 1 = 0 := by omega
    simp only [heq1, Nat.choose_self, Nat.cast_one, heq2, pow_zero, mul_one]
    simp only [P, Ideal.mem_span_singleton]
    intro h_dvd
    have : p ∣ 1 := by
      have h1 : (1 : ℤ) = ((1 : ℕ) : ℤ) := by norm_cast
      rw [h1] at h_dvd
      exact Int.natCast_dvd_natCast.mp h_dvd
    exact hp_prime.not_dvd_one this

  -- Step 12: Construct the Eisenstein witness
  have hg_eisenstein : g.IsEisensteinAt P := by
    exact Polynomial.Monic.isEisensteinAt_of_mem_of_notMem hg_monic hP_ne_top
      (fun {n} hn => hg_lower_coeffs_in_P n hn) hg_const_not_in_P2

  -- Step 13: g is primitive (since it's monic)
  have hg_primitive : g.IsPrimitive := hg_monic.isPrimitive

  -- Step 14: Apply Eisenstein's criterion
  have hg_degree_pos : 0 < g.natDegree := by
    rw [hg_degree]
    omega

  exact Polynomial.IsEisensteinAt.irreducible hg_eisenstein hP_prime hg_primitive hg_degree_pos
