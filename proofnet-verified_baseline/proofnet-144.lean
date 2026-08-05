import Mathlib

open scoped BigOperators



/-Informal Statement

Prove that for each positive integer $n$, the number $10^{10^{10^n}}+10^{10^n}+10^n-1$ is not prime.
-/

/-Informal Proof

Put
\[
N = 10^{10^{10^n}} + 10^{10^n} + 10^n - 1.
\]
Write $n = 2^m k$ with $m$ a nonnegative integer and $k$ a positive odd integer.
For any nonnegative integer $j$,
\[
10^{2^m j} \equiv (-1)^j \pmod{10^{2^m} + 1}.
\]
Since $10^n \geq n \geq 2^m \geq m+1$, $10^n$ is divisible by $2^n$ and hence by $2^{m+1}$,
and similarly $10^{10^n}$ is divisible by $2^{10^n}$ and hence by $2^{m+1}$. It follows that
\[
N \equiv 1 + 1 + (-1) + (-1) \equiv 0 \pmod{10^{2^m} + 1}.
\]
Since $N \geq 10^{10^n} > 10^n + 1 \geq 10^{2^m} + 1$, it follows that $N$ is composite.
-/

/-
Formal Proof Strategy:
1. Write n = 2^m * k where k is odd (use Nat.exists_eq_two_pow_mul_odd)
2. Let d = 10^(2^m) + 1, this is our candidate divisor
3. Show modulo d:
   - 10^(2^m) ≡ -1 (mod d)
   - 10^n = (10^(2^m))^k ≡ (-1)^k = -1 (mod d) since k is odd
   - 10^(10^n) = (10^(2^m))^(10^n / 2^m) ≡ 1 (mod d) since 10^n / 2^m is even
   - 10^(10^(10^n)) ≡ 1 (mod d) similarly
4. So N ≡ 1 + 1 + (-1) - 1 = 0 (mod d)
5. Show d ≥ 2 and d < N, conclude N is not prime
-/

-- Lemma: a ≡ -1 (mod a + 1)
-- This is because a + 1 ≡ 0 (mod a + 1), so a ≡ -1 (mod a + 1)
lemma a_eq_neg_one_mod (a : ℕ) : (a : ZMod (a + 1)) = -1 := by
  have h : (a : ZMod (a + 1)) + 1 = 0 := by
    have : ((a + 1 : ℕ) : ZMod (a + 1)) = 0 := ZMod.natCast_self (a + 1)
    simp only [Nat.cast_add, Nat.cast_one] at this
    exact this
  exact eq_neg_of_add_eq_zero_left h

-- Helper: 10^n = 2^n * 5^n
-- Used to analyze the 2-adic valuation of 10^n
lemma ten_pow_eq (n : ℕ) : (10 : ℕ)^n = 2^n * 5^n := by
  have h : (10 : ℕ) = 2 * 5 := by norm_num
  calc (10 : ℕ)^n = (2 * 5)^n := by rw [h]
    _ = 2^n * 5^n := by rw [mul_pow]

-- Main theorem: 10^(10^(10^n)) + 10^(10^n) + 10^n - 1 is not prime for n > 0
theorem Putnam_exercise_2010_a4 (n : ℕ) (hn : n > 0) :
    ¬ Nat.Prime (10^10^10^n + 10^10^n + 10^n - 1) := by
  -- Step 1: Factor n = 2^m * k where k is odd
  -- Every positive integer can be uniquely written as 2^m * k with k odd
  have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  obtain ⟨m, k, hk_odd, hn_eq⟩ := Nat.exists_eq_two_pow_mul_odd hn_ne

  -- Step 2: Define the divisor d = 10^(2^m) + 1
  -- This will be a non-trivial divisor of N
  set d := 10^(2^m) + 1 with hd_def
  set b := 10^(2^m) with hb_def

  -- Step 3: We will show d divides N using ZMod arithmetic
  -- Key observation: b ≡ -1 (mod d) since d = b + 1

  -- Step 3.1: 10^n ≡ -1 (mod d) since n = 2^m * k and k is odd
  -- We have 10^n = (10^(2^m))^k = b^k ≡ (-1)^k = -1 (mod d)
  have h_10n_mod : (10^n : ZMod d) = -1 := by
    -- First establish that 10^n = b^k in natural numbers
    have h_pow : (10 : ℕ)^n = b^k := by
      rw [hn_eq, hb_def, ← pow_mul]
    -- b ≡ -1 (mod d) by the lemma a_eq_neg_one_mod
    have h_base : (b : ZMod d) = -1 := a_eq_neg_one_mod b
    -- Get the equality in ZMod d
    have h_cast : ((10 : ZMod d)^n : ZMod d) = ((b^k : ℕ) : ZMod d) := by
      change ((10 : ℕ) : ZMod d)^n = ((b^k : ℕ) : ZMod d)
      norm_cast
      exact congrArg (Nat.cast (R := ZMod d)) h_pow
    -- Now chain the equalities
    calc (10^n : ZMod d) = ((b^k : ℕ) : ZMod d) := h_cast
      _ = (b : ZMod d)^k := by norm_cast
      _ = (-1 : ZMod d)^k := by rw [h_base]
      _ = -1 := hk_odd.neg_one_pow

  -- Step 3.2: Establish bounds for showing 10^(10^n) has enough factors of 2
  -- We need m < 10^n to ensure 2^m divides 10^n
  have h_10n_gt_m : m < 10^n := by
    calc m < 2^m := Nat.lt_two_pow_self
      _ ≤ 2^m * k := Nat.le_mul_of_pos_right _ hk_odd.pos
      _ = n := hn_eq.symm
      _ < 10^n := Nat.lt_pow_self (by norm_num : 1 < 10)

  -- We also need m < n for divisibility arguments
  -- This follows from n = 2^m * k ≥ 2^m > m (for m ≥ 1) or n = k ≥ 1 > 0 = m (for m = 0)
  have h_n_gt_m : m < n := by
    cases' Nat.eq_zero_or_pos m with hm0 hm_pos
    · simp [hm0]; exact hn
    · calc m < 2^m := Nat.lt_two_pow_self
        _ ≤ 2^m * k := Nat.le_mul_of_pos_right _ hk_odd.pos
        _ = n := hn_eq.symm

  -- 2^m divides 10^n because 10^n = 2^n * 5^n and m < n implies 2^m | 2^n
  have h_2m_dvd_10n : 2^m ∣ 10^n := by
    have h1 : 2^m ∣ 2^n := Nat.pow_dvd_pow 2 (Nat.le_of_lt h_n_gt_m)
    have h2 : (2 : ℕ)^n ∣ 10^n := by
      rw [ten_pow_eq]
      exact Nat.dvd_mul_right _ _
    exact Nat.dvd_trans h1 h2

  -- 10^n / 2^m is even because n > m means 10^n has at least m+1 factors of 2
  -- Specifically, 10^n / 2^m = 2^(n-m) * 5^n, and 2^(n-m) is even when n > m
  have h_even_quot : Even (10^n / 2^m) := by
    -- First show the quotient formula
    have h_eq : 10^n / 2^m = 2^(n - m) * 5^n := by
      rw [ten_pow_eq]
      have h_dvd : 2^m ∣ 2^n := Nat.pow_dvd_pow 2 (Nat.le_of_lt h_n_gt_m)
      rw [Nat.mul_comm (2^n) (5^n), Nat.mul_div_assoc _ h_dvd, Nat.mul_comm]
      congr 1
      exact Nat.pow_div (Nat.le_of_lt h_n_gt_m) (by norm_num : 0 < 2)
    rw [h_eq]
    have h_nm_pos : 0 < n - m := Nat.sub_pos_of_lt h_n_gt_m
    -- 2^(n-m) is even since n - m ≥ 1
    have h_even_power : Even (2^(n - m)) := by
      refine ⟨2^(n - m - 1), ?_⟩
      have hsub : n - m - 1 + 1 = n - m := Nat.sub_add_cancel h_nm_pos
      calc 2^(n - m) = 2^(n - m - 1 + 1) := by rw [hsub]
        _ = 2^(n - m - 1) * 2 := by ring
        _ = 2^(n - m - 1) + 2^(n - m - 1) := by ring
    exact Even.mul_right h_even_power _

  -- Step 3.3: 10^(10^n) ≡ 1 (mod d) since the quotient 10^n / 2^m is even
  -- We have 10^(10^n) = b^(10^n / 2^m) ≡ (-1)^(even) = 1 (mod d)
  have h_10_10n_mod : (10^(10^n) : ZMod d) = 1 := by
    -- First establish that 10^(10^n) = b^(10^n / 2^m) in natural numbers
    have h_pow : (10 : ℕ)^(10^n) = b^(10^n / 2^m) := by
      rw [hb_def, ← pow_mul]
      congr 1
      exact (Nat.mul_div_cancel' h_2m_dvd_10n).symm
    have h_base : (b : ZMod d) = -1 := a_eq_neg_one_mod b
    have h_cast : ((10 : ZMod d)^(10^n) : ZMod d) = ((b^(10^n / 2^m) : ℕ) : ZMod d) := by
      change ((10 : ℕ) : ZMod d)^(10^n) = ((b^(10^n / 2^m) : ℕ) : ZMod d)
      norm_cast
      exact congrArg (Nat.cast (R := ZMod d)) h_pow
    calc (10^(10^n) : ZMod d) = ((b^(10^n / 2^m) : ℕ) : ZMod d) := h_cast
      _ = (b : ZMod d)^(10^n / 2^m) := by norm_cast
      _ = (-1 : ZMod d)^(10^n / 2^m) := by rw [h_base]
      _ = 1 := h_even_quot.neg_one_pow

  -- Step 3.4: Similarly, 10^(10^(10^n)) ≡ 1 (mod d)
  -- We need m < 10^(10^n) and 10^(10^n) / 2^m to be even
  have h_m_lt_10_10n : m < 10^(10^n) :=
    Nat.lt_trans h_10n_gt_m (Nat.lt_pow_self (by norm_num : 1 < 10))

  have h_2m_dvd_10_10n : 2^m ∣ 10^(10^n) := by
    have h1 : 2^m ∣ 2^(10^n) := Nat.pow_dvd_pow 2 (Nat.le_of_lt h_10n_gt_m)
    have h2 : (2 : ℕ)^(10^n) ∣ 10^(10^n) := by
      have h_eq : (10 : ℕ)^(10^n) = 2^(10^n) * 5^(10^n) := ten_pow_eq (10^n)
      rw [h_eq]
      exact Nat.dvd_mul_right _ _
    exact Nat.dvd_trans h1 h2

  have h_even_quot' : Even (10^(10^n) / 2^m) := by
    have h_eq : 10^(10^n) / 2^m = 2^(10^n - m) * 5^(10^n) := by
      have h_eq' : (10 : ℕ)^(10^n) = 2^(10^n) * 5^(10^n) := ten_pow_eq (10^n)
      rw [h_eq']
      have h_dvd : 2^m ∣ 2^(10^n) := Nat.pow_dvd_pow 2 (Nat.le_of_lt h_10n_gt_m)
      rw [Nat.mul_comm (2^(10^n)) (5^(10^n)), Nat.mul_div_assoc _ h_dvd, Nat.mul_comm]
      congr 1
      exact Nat.pow_div (Nat.le_of_lt h_10n_gt_m) (by norm_num : 0 < 2)
    rw [h_eq]
    have h_nm_pos : 0 < 10^n - m := Nat.sub_pos_of_lt h_10n_gt_m
    have h_even_power : Even (2^(10^n - m)) := by
      refine ⟨2^(10^n - m - 1), ?_⟩
      have hsub : 10^n - m - 1 + 1 = 10^n - m := Nat.sub_add_cancel h_nm_pos
      calc 2^(10^n - m) = 2^(10^n - m - 1 + 1) := by rw [hsub]
        _ = 2^(10^n - m - 1) * 2 := by ring
        _ = 2^(10^n - m - 1) + 2^(10^n - m - 1) := by ring
    exact Even.mul_right h_even_power _

  have h_10_10_10n_mod : (10^(10^(10^n)) : ZMod d) = 1 := by
    -- 10^(10^(10^n)) = b^(10^(10^n) / 2^m) ≡ (-1)^(even) = 1 (mod d)
    have h_pow : (10 : ℕ)^(10^(10^n)) = b^(10^(10^n) / 2^m) := by
      rw [hb_def, ← pow_mul]
      congr 1
      exact (Nat.mul_div_cancel' h_2m_dvd_10_10n).symm
    have h_base : (b : ZMod d) = -1 := a_eq_neg_one_mod b
    have h_cast : ((10 : ZMod d)^(10^(10^n)) : ZMod d) = ((b^(10^(10^n) / 2^m) : ℕ) : ZMod d) := by
      change ((10 : ℕ) : ZMod d)^(10^(10^n)) = ((b^(10^(10^n) / 2^m) : ℕ) : ZMod d)
      norm_cast
      exact congrArg (Nat.cast (R := ZMod d)) h_pow
    calc (10^(10^(10^n)) : ZMod d) = ((b^(10^(10^n) / 2^m) : ℕ) : ZMod d) := h_cast
      _ = (b : ZMod d)^(10^(10^n) / 2^m) := by norm_cast
      _ = (-1 : ZMod d)^(10^(10^n) / 2^m) := by rw [h_base]
      _ = 1 := h_even_quot'.neg_one_pow

  -- Step 4: Show d | N
  -- N = 10^(10^(10^n)) + 10^(10^n) + 10^n - 1
  -- ≡ 1 + 1 + (-1) - 1 = 0 (mod d)

  -- First establish that the expression is ≥ 1 so subtraction is valid in ℕ
  have h_N_ge_1 : 10^10^10^n + 10^10^n + 10^n ≥ 1 := by
    have h1 : (10 : ℕ)^n ≥ 1 := Nat.one_le_pow _ _ (by norm_num)
    have h2 : (10 : ℕ)^(10^n) ≥ 1 := Nat.one_le_pow _ _ (by norm_num)
    have h3 : (10 : ℕ)^(10^(10^n)) ≥ 1 := Nat.one_le_pow _ _ (by norm_num)
    linarith

  have h_d_dvd_N : d ∣ 10^10^10^n + 10^10^n + 10^n - 1 := by
    have h_cast : ((10^10^10^n + 10^10^n + 10^n - 1 : ℕ) : ZMod d) = 0 := by
      rw [Nat.cast_sub h_N_ge_1]
      push_cast
      -- After push_cast, we have expressions like (10 : ZMod d)^...
      -- Use the modular arithmetic results established above
      rw [h_10_10_10n_mod, h_10_10n_mod, h_10n_mod]
      ring
    exact (ZMod.natCast_eq_zero_iff _ _).mp h_cast

  -- Step 5: Show d ≥ 2 (the divisor is non-trivial)
  have h_d_ge_2 : 2 ≤ d := by
    have : 10^(2^m) ≥ 1 := Nat.one_le_pow _ _ (by norm_num)
    omega

  -- Step 6: Show d < N (the divisor is strictly smaller than N)
  -- d = 10^(2^m) + 1 ≤ 10^n + 1 < 10^(10^n) < N
  have h_d_lt_N : d < 10^10^10^n + 10^10^n + 10^n - 1 := by
    -- 10^(2^m) ≤ 10^n since 2^m ≤ n
    have h1 : 10^(2^m) ≤ 10^n := by
      apply Nat.pow_le_pow_right (by norm_num : 1 ≤ 10)
      calc 2^m ≤ 2^m * k := Nat.le_mul_of_pos_right _ hk_odd.pos
        _ = n := hn_eq.symm
    have h2 : d ≤ 10^n + 1 := by omega
    -- 10^n + 1 < 10^(10^n) since n + 1 ≤ 10^n
    have h_10n_ge_2 : 10^n ≥ 2 := by
      calc 10^n ≥ 10^1 := Nat.pow_le_pow_right (by norm_num) hn
        _ = 10 := by norm_num
        _ ≥ 2 := by norm_num
    have h3 : 10^n + 1 < 10^(10^n) := by
      -- First show n + 1 ≤ 10^n using n < 10^n
      have h_n_lt_10n : n < 10^n := Nat.lt_pow_self (by norm_num : 1 < 10)
      have h_n_plus_1_le : n + 1 ≤ 10^n := by omega
      -- Now show 10^n + 1 < 10^(10^n)
      -- Since 10^n ≥ 10 for n ≥ 1, we have 10^n + 1 ≤ 2 * 10^n < 10 * 10^n = 10^(n+1) ≤ 10^(10^n)
      have h_10n_ge_1 : 1 ≤ 10^n := Nat.one_le_pow _ _ (by norm_num)
      calc 10^n + 1 ≤ 10^n + 10^n := by omega
        _ = 2 * 10^n := by ring
        _ < 10 * 10^n := by omega
        _ = 10^(n + 1) := by ring
        _ ≤ 10^(10^n) := Nat.pow_le_pow_right (by norm_num) h_n_plus_1_le
    have h4 : 10^(10^n) ≤ 10^10^10^n + 10^10^n + 10^n - 1 := by
      have h_n_le_10n : n ≤ 10^n := (Nat.lt_pow_self (by norm_num : 1 < 10) : n < 10^n).le
      have h_10n_le : 10^n ≤ 10^(10^n) := Nat.pow_le_pow_right (by norm_num) h_n_le_10n
      have h_big : 10^10^10^n ≥ 10^(10^n) := by
        apply Nat.pow_le_pow_right (by norm_num : 1 ≤ 10)
        exact h_10n_le
      have h_10_10n_ge_1 : (10 : ℕ)^(10^n) ≥ 1 := Nat.one_le_pow _ _ (by norm_num)
      have h_10n_ge_1 : (10 : ℕ)^n ≥ 1 := Nat.one_le_pow _ _ (by norm_num)
      omega
    omega

  -- Step 7: Conclude N is not prime using Nat.not_prime_of_dvd_of_lt
  -- Since d | N, 2 ≤ d, and d < N, N cannot be prime
  exact Nat.not_prime_of_dvd_of_lt h_d_dvd_N h_d_ge_2 h_d_lt_N
