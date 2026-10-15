import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators



/-Informal Statement

Prove that if a prime integer $p$ has the form $2^r+1$, then it actually has the form $2^{2^k}+1$.
-/

/-Informal Proof

In particular, we have
$$
\frac{x^a+1}{x+1}=\frac{(-x)^a-1}{(-x)-1}=1-x+x^2-\cdots+(-x)^{a-1}
$$
by the geometric sum formula. In this case, specialize to $x=2^{2^m}$ and we have a nontrivial divisor.
-/

theorem Artin_exercise_13_4_10
    {p : ℕ} {hp : Nat.Prime p} (h : ∃ r : ℕ, p = 2 ^ r + 1) :
    ∃ (k : ℕ), p = 2 ^ (2 ^ k) + 1 := by
  sorry

/-
Step 0: Diagnose the gap.
The original formal statement fails for the prime number `p = 2`.  Setting `r = 0`
gives `p = 2 ^ 0 + 1 = 2`, which is a prime, but `2` is strictly smaller than every
number of the form `2 ^ (2 ^ k) + 1`, because `2 ^ (2 ^ k) ≥ 2` for all `k`, so
`2 ^ (2 ^ k) + 1 ≥ 3`.  Hence the missing hypothesis is that the exponent `r`
must be positive (equivalently, that `p ≠ 2`).  The proofs below first formalize
this counterexample, negate the original statement, and then prove the corrected
version with the necessary positivity assumption on `r`.
-/
lemma odd_pow_plus_one_dvd {a m : ℕ} (hm : Odd m) :
    a + 1 ∣ a ^ m + 1 := by
  classical
  -- Step 1: Work modulo the candidate divisor `a + 1`.
  have h_cast :
      ((a ^ m + 1 : ℕ) : ZMod (a + 1)) =
        (a : ZMod (a + 1)) ^ m + 1 := by
    -- Step 1.1: Casting preserves addition and powers.
    simp
  -- Step 2: Identify `(a : ZMod (a + 1))` with `-1`.
  have h_sum :
      (a : ZMod (a + 1)) + 1 = (0 : ZMod (a + 1)) := by
    -- Step 2.1: Rewrite the cast of `a + 1`.
    have h_add :
        ((a + 1 : ℕ) : ZMod (a + 1)) =
          (a : ZMod (a + 1)) + (1 : ZMod (a + 1)) := by
      simp
    -- Step 2.2: Reduce modulo `a + 1`.
    simp
  have h_eq :
      (a : ZMod (a + 1)) = (-1 : ZMod (a + 1)) := by
    -- Step 2.3: Rearrange the equality so the lemma applies directly.
    have h_symm :
        (1 : ZMod (a + 1)) + (a : ZMod (a + 1)) = 0 := by
      simp [add_comm]
    simpa using eq_neg_of_add_eq_zero_right h_symm
  -- Step 3: Evaluate the odd power of `-1`.
  have h_pow :
      (a : ZMod (a + 1)) ^ m = (-1 : ZMod (a + 1)) := by
    simpa [h_eq] using hm.neg_one_pow
  -- Step 4: The cast of `a ^ m + 1` vanishes modulo `a + 1`.
  have h_zero :
      ((a ^ m + 1 : ℕ) : ZMod (a + 1)) = 0 := by
    simp [h_cast, h_pow, add_comm]
  -- Step 5: Convert the congruence back to divisibility in `ℕ`.
  exact (ZMod.natCast_eq_zero_iff (a ^ m + 1) (a + 1)).1 h_zero

theorem Artin_exercise_13_4_10_neg :
    ¬ (∀ p : ℕ, Nat.Prime p → (∃ r : ℕ, p = 2 ^ r + 1) →
        ∃ k : ℕ, p = 2 ^ (2 ^ k) + 1) := by
  classical
  -- Step 1: Focus on the specific prime `p = 2`.
  refine not_forall.mpr ?_
  refine ⟨2, ?_⟩
  -- Step 2: Produce the counterexample data at `p = 2`.
  have hPrime : Nat.Prime 2 := Nat.prime_two
  have hWitness : ∃ r : ℕ, 2 = 2 ^ r + 1 := by
    -- Step 2.1: Choose `r = 0`.
    refine ⟨0, by simp⟩
  have hImpossible :
      ¬ (∃ k : ℕ, 2 = 2 ^ (2 ^ k) + 1) := by
    -- Step 2.2: Any right-hand side is strictly larger than `2`.
    refine not_exists.mpr ?_
    intro k
    -- Step 2.2.1: Bound `2 ^ (2 ^ k)` below by `2`.
    have hTwoLe : 2 ≤ 2 ^ (2 ^ k) := by
      have hBase : 1 ≤ (2 : ℕ) := by decide
      have hExp : 1 ≤ 2 ^ k := by
        exact Nat.succ_le_of_lt (pow_pos (by decide : (0 : ℕ) < 2) k)
      exact pow_le_pow_right' (a := (2 : ℕ)) hBase hExp
    -- Step 2.2.2: Conclude strict inequality after adding `1`.
    have hStrict : 2 < 2 ^ (2 ^ k) + 1 :=
      Nat.lt_of_le_of_lt hTwoLe (lt_add_one _)
    -- Step 2.2.3: Strict inequality prevents equality with `2`.
    exact ne_of_lt hStrict
  -- Step 3: Assemble the contradiction to the implication.
  refine Classical.not_imp.mpr ?_
  refine ⟨hPrime, ?_⟩
  refine Classical.not_imp.mpr ?_
  exact ⟨hWitness, hImpossible⟩

theorem Artin_exercise_13_4_10_corrected
    {p : ℕ} (hp : Nat.Prime p)
    (h : ∃ r : ℕ, 1 ≤ r ∧ p = 2 ^ r + 1) :
    ∃ k : ℕ, p = 2 ^ (2 ^ k) + 1 := by
  classical
  -- Step 1: Extract the exponent and note its positivity.
  obtain ⟨r, hr_pos, hr_def⟩ := h
  have hr_ne_zero : r ≠ 0 := by
    -- Step 1.1: A positive natural cannot be zero.
    exact fun hr0 => by simp [hr0] at hr_pos
  -- Step 2: Factor `r` as a power of two times an odd part.
  obtain ⟨k, t, htOdd, hr_factor⟩ := Nat.exists_eq_two_pow_mul_odd hr_ne_zero
  have hr_factor_eq : r = 2 ^ k * t := hr_factor
  -- Step 3: Record a convenient expression for the prime `p`.
  have hp_repr :
      p = (2 ^ (2 ^ k)) ^ t + 1 := by
    -- Step 3.1: Substitute the factorisation of `r`.
    have hPow :
        2 ^ (t * 2 ^ k) = (2 ^ (2 ^ k)) ^ t := by
      have : 2 ^ (2 ^ k * t) = (2 ^ (2 ^ k)) ^ t :=
        by simpa using (pow_mul (2 : ℕ) (2 ^ k) t)
      simpa [Nat.mul_comm] using this
    simp [hr_def, hr_factor_eq, Nat.mul_comm, hPow]
  -- Step 4: Show that `2 ^ (2 ^ k) + 1` divides `p`.
  have h_div :
      2 ^ (2 ^ k) + 1 ∣ p := by
    -- Step 4.1: Apply the divisibility lemma to the odd exponent `t`.
    have h_aux :
        2 ^ (2 ^ k) + 1 ∣ (2 ^ (2 ^ k)) ^ t + 1 :=
      odd_pow_plus_one_dvd htOdd
    -- Step 4.2: Transfer divisibility along the identified equality.
    simpa [hp_repr] using h_aux
  -- Step 5: Establish that the divisor exceeds `1`.
  have h_gt_one : 1 < 2 ^ (2 ^ k) + 1 := by
    -- Step 5.1: Any positive natural remains positive after adding `1`.
    have h_pos : 0 < 2 ^ (2 ^ k) := pow_pos (by decide : (0 : ℕ) < 2) (2 ^ k)
    simp
  -- Step 6: Prove that the odd component `t` must equal `1`.
  have ht_eq_one : t = 1 := by
    -- Step 6.1: Assume for contradiction that `t ≠ 1`.
    by_contra ht_ne_one
    -- Step 6.2: Obtain a strict upper bound for the divisor.
    have h_lt_p : 2 ^ (2 ^ k) + 1 < p := by
      -- Step 6.2.1: Ensure `t` is strictly larger than `1`.
      have ht_gt_one : 1 < t := by
        exact (Nat.one_lt_iff_ne_zero_and_ne_one).2
          ⟨ne_of_gt htOdd.pos, ht_ne_one⟩
      -- Step 6.2.2: Compare the exponents `2 ^ k` and `2 ^ k * t`.
      have h_exp_lt : 2 ^ k < 2 ^ k * t := by
        have hPos : 0 < 2 ^ k := pow_pos (by decide : (0 : ℕ) < 2) k
        have hMul : 2 ^ k * 1 < 2 ^ k * t :=
          Nat.mul_lt_mul_of_pos_left ht_gt_one hPos
        simpa using hMul
      -- Step 6.2.3: Lift the inequality through the power function.
      have h_pow_lt :
          2 ^ (2 ^ k) < 2 ^ (2 ^ k * t) :=
        Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) h_exp_lt
      -- Step 6.2.4: Add `1` and use the description of `p`.
      have h_pow_add :
          2 ^ (2 ^ k) + 1 < 2 ^ (2 ^ k * t) + 1 :=
        Nat.add_lt_add_right h_pow_lt _
      simpa [hr_def, hr_factor_eq, Nat.mul_comm] using h_pow_add
    -- Step 6.3: Primality rules out both possible divisors.
    have h_ne_one : 2 ^ (2 ^ k) + 1 ≠ 1 := ne_of_gt h_gt_one
    have h_ne_p : 2 ^ (2 ^ k) + 1 ≠ p := ne_of_lt h_lt_p
    cases (Nat.dvd_prime hp).1 h_div with
    | inl h1 => exact h_ne_one h1
    | inr h2 => exact h_ne_p h2
  -- Step 7: Replace `t` with `1` and deduce that `r` is a power of two.
  have hr_power : r = 2 ^ k := by
    simp [hr_factor_eq, ht_eq_one]
  -- Step 8: Substitute back into the original description of `p`.
  refine ⟨k, ?_⟩
  simp [hr_def, hr_power]
