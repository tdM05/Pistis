import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that if an integer is the sum of two rational squares, then it is the sum of two integer squares.
-/

/-Informal Proof

Let $n=\frac{a^2}{b^2}+\frac{c^2}{d^2}$, or, equivalently, $n(b d)^2=a^2 d^2+c^2 b^2$. From this, we see that $n(b d)^2$ can be written as a sum of two squared integers. Therefore, if $q \equiv 3(\bmod 4)$ and $q^i$ appears in the prime power factorization of $n, i$ must be even. Let $j \in \mathbb{N} \cup\{0\}$ such that $q^j$ divides $b d$. Then $q^{i-2 j}$ divides $n$. But since $i$ is even, $i-2 j$ is even as well. Consequently, $n$ can be written as a sum of two squared integers.
-/

theorem Dummit_Foote_exercise_8_3_4 {n : ℤ} {r s : ℚ}
  (h : r^2 + s^2 = n) :
  ∃ a b : ℤ, a^2 + b^2 = n := by
  classical
  /- Step 0: Split off the easy zero case for `n`. -/
  by_cases hn : n = 0
  · /- Step 0.1: When `n = 0`, take the obvious witnesses `0` and `0`. -/
    refine ⟨0, 0, by simp [hn]⟩
  /- Step 1: Show that the integer `n` is non‑negative, since it is a sum of squares. -/
  have hn_nonneg : 0 ≤ n := by
    -- Step 1.1: Each square in ℚ is non‑negative, so their sum is non‑negative.
    have hsum_nonneg : (0 : ℚ) ≤ r ^ 2 + s ^ 2 := by
      have hr := sq_nonneg r
      have hs := sq_nonneg s
      nlinarith
    -- Step 1.2: Transport the inequality from ℚ back to ℤ using the identity `h`.
    have : (0 : ℚ) ≤ n := by simpa [h] using hsum_nonneg
    exact_mod_cast this
  /- Step 2: Fix a common positive denominator and the corresponding integer numerators. -/
  -- Step 2.1: Choose the common denominator `d = r.den * s.den`.
  set d : ℕ := r.den * s.den with hdDef
  have hd_pos : 0 < d := by
    -- Both denominators are positive by definition.
    have := Nat.mul_pos r.den_pos s.den_pos
    simpa [hdDef] using this
  -- Step 2.2: Define the cleared numerators `x` and `y` in ℤ.
  let x : ℤ := r.num * s.den
  let y : ℤ := s.num * r.den
  /- Step 3: Clear denominators in the equality `r^2 + s^2 = n`
     to obtain an integer identity. -/
  have h_int :
      (x ^ 2 + y ^ 2 : ℤ) = n * (d ^ 2 : ℤ) := by
    -- Step 3.1: Rewrite `r` and `s` explicitly as `num / den`.
    have h' :
        ((r.num : ℚ) / r.den) ^ 2 + ((s.num : ℚ) / s.den) ^ 2 = (n : ℚ) := by
      simpa [Rat.num_div_den] using h
    -- Step 3.2: Clear denominators; now they are explicit.
    have h'' := h'
    field_simp [pow_two, hdDef] at h''
    -- Step 3.3: Rephrase the cleared equality using the abbreviations `x`, `y`, and `d`.
    -- After `field_simp`, both sides live in ℤ.
    have h''' :
        r.num ^ 2 * (s.den : ℤ) ^ 2 + s.num ^ 2 * (r.den : ℤ) ^ 2 =
          n * (d ^ 2 : ℤ) := by
      -- The cleared equality lives in ℚ; simplify casts to see it in ℤ.
      have h'''' : (r.num ^ 2 * (s.den : ℤ) ^ 2 + (r.den : ℤ) ^ 2 * s.num ^ 2 : ℚ) =
          (n : ℚ) * (d : ℚ) ^ 2 := by
        -- `field_simp` already multiplied by `(r.den * s.den)^2 = d^2`.
        simpa [pow_two, hdDef, mul_comm, mul_left_comm, mul_assoc] using h''
      -- Reorder the second term to match the target orientation and cast down to ℤ.
      have h''''' : (r.num ^ 2 * (s.den : ℤ) ^ 2 + s.num ^ 2 * (r.den : ℤ) ^ 2 : ℚ) =
          (n : ℚ) * (d : ℚ) ^ 2 := by
        simpa [mul_comm] using h''''
      exact_mod_cast h'''''
    -- Step 3.4: Replace the expanded products by the squares of `x` and `y`,
    -- and recognise the right‑hand side as `n * d^2`.
    calc
      (x ^ 2 + y ^ 2 : ℤ)
          = r.num ^ 2 * (s.den : ℤ) ^ 2 + s.num ^ 2 * (r.den : ℤ) ^ 2 := by
            -- Expand each square of a product separately.
            have hx_sq : x ^ 2 = r.num ^ 2 * (s.den : ℤ) ^ 2 := by
              dsimp [x]
              ring
            have hy_sq : y ^ 2 = s.num ^ 2 * (r.den : ℤ) ^ 2 := by
              dsimp [y]
              ring
            -- Replace `x ^ 2` and `y ^ 2` using the two identities.
            simp [hx_sq, hy_sq]
      _ = n * (d ^ 2 : ℤ) := h'''
  /- Step 4: Move to natural numbers so that we can invoke the sum‑of‑two‑squares
     characterization from number theory. -/
  -- Step 4.1: Interpret the left and right of `h_int` as natural numbers (they are non‑negative).
  have hx_sq_nonneg : (0 : ℤ) ≤ x ^ 2 := by exact sq_nonneg _
  have hy_sq_nonneg : (0 : ℤ) ≤ y ^ 2 := by exact sq_nonneg _
  have h_rhs_nonneg : (0 : ℤ) ≤ n * (d ^ 2 : ℤ) := by
    -- Both factors are non‑negative: `n` by Step 1 and `d^2` trivially.
    have hd2_nonneg : (0 : ℤ) ≤ (d ^ 2 : ℤ) := by
      have : (0 : ℕ) ≤ d ^ 2 := Nat.zero_le _
      exact_mod_cast this
    exact mul_nonneg hn_nonneg hd2_nonneg
  -- Step 4.2: Replace squares by squares of absolute values, then descend to ℕ.
  have h_int_natAbs :
      (x.natAbs : ℤ) ^ 2 + (y.natAbs : ℤ) ^ 2 = (n.natAbs : ℤ) * (d ^ 2 : ℤ) := by
    -- Step 4.2.1: Squares ignore signs, so we can pass to absolute values.
    have hx_sq : (x.natAbs : ℤ) ^ 2 = x ^ 2 := by
      have hx_abs : (x.natAbs : ℤ) = |x| := by simp
      simp [hx_abs]
    have hy_sq : (y.natAbs : ℤ) ^ 2 = y ^ 2 := by
      have hy_abs : (y.natAbs : ℤ) = |y| := by simp
      simp [hy_abs]
    have hn_abs : (n.natAbs : ℤ) = n := by
      -- `n` is non‑negative by Step 1, so its absolute value is itself.
      have := abs_of_nonneg hn_nonneg
      simpa using this
    calc
      (x.natAbs : ℤ) ^ 2 + (y.natAbs : ℤ) ^ 2
          = x ^ 2 + y ^ 2 := by simp
      _ = n * (d ^ 2 : ℤ) := h_int
      _ = (n.natAbs : ℤ) * (d ^ 2 : ℤ) := by simp [hn_abs]
  have h_nat :
      n.natAbs * d ^ 2 =
        (Int.natAbs x) ^ 2 + (Int.natAbs y) ^ 2 := by
    -- Cast the integer equality with absolute values down to ℕ.
    exact_mod_cast h_int_natAbs.symm
  -- Step 4.3: Package the explicit witnesses for the product being a sum of two squares.
  have h_exists_prod :
      ∃ a b : ℕ, n.natAbs * d ^ 2 = a ^ 2 + b ^ 2 :=
    ⟨Int.natAbs x, Int.natAbs y, h_nat⟩
  /- Step 5: Use the parity characterization `Nat.eq_sq_add_sq_iff`
     to deduce that `n.natAbs` itself is a sum of two squares. -/
  -- Step 5.1: Extract the “even valuation at primes 3 mod 4” property for the product.
  have h_even_prod :
      ∀ q ∈ (n.natAbs * d ^ 2).primeFactors, q % 4 = 3 →
        Even (padicValNat q (n.natAbs * d ^ 2)) :=
    (Nat.eq_sq_add_sq_iff (n := n.natAbs * d ^ 2)).mp h_exists_prod
  -- Step 5.2: Show the same evenness property for `n.natAbs` alone.
  have h_even_n :
      ∀ q ∈ n.natAbs.primeFactors, q % 4 = 3 → Even (padicValNat q n.natAbs) := by
    intro q hq_mem hq4
    -- Extract primality and divisibility from membership in primeFactors.
    have hq := Nat.prime_of_mem_primeFactors hq_mem
    -- Show q is in primeFactors of the product via monotonicity.
    have hprod_ne : n.natAbs * d ^ 2 ≠ 0 :=
      mul_ne_zero (fun h => hn (Int.natAbs_eq_zero.mp h))
        (pow_ne_zero _ (Nat.ne_of_gt hd_pos))
    have hq_mem_prod : q ∈ (n.natAbs * d ^ 2).primeFactors :=
      Nat.primeFactors_mono (dvd_mul_right n.natAbs (d ^ 2)) hprod_ne hq_mem
    have h_even_prod_q := h_even_prod q hq_mem_prod hq4
    -- Compute the valuation of the product as the sum of valuations.
    have hd_ne_zero : d ^ 2 ≠ 0 := by
      exact pow_ne_zero _ (Nat.ne_of_gt hd_pos)
    -- Register the primality instance required by `padicValNat.mul` and `pow`.
    haveI : Fact q.Prime := ⟨hq⟩
    -- Split into the zero and non‑zero cases for `n.natAbs`.
    by_cases hzero : n.natAbs = 0
    · -- If `n = 0`, the valuation is 0 and hence even.
      simp [hzero]
    · -- Otherwise we can use the multiplicative rule for valuations.
      have h_val :
          padicValNat q (n.natAbs * d ^ 2) =
            padicValNat q n.natAbs + padicValNat q (d ^ 2) :=
        padicValNat.mul (p := q) (a := n.natAbs) (b := d ^ 2) hzero hd_ne_zero
      -- The second summand is even because it is twice a valuation.
      have h_even_dsq : Even (padicValNat q (d ^ 2)) := by
        have hd_ne : d ≠ 0 := Nat.ne_of_gt hd_pos
        -- Use the power rule: v_q(d^2) = 2 * v_q(d).
        have hpow := padicValNat.pow (p := q) (a := d) (n := 2) hd_ne
        -- Conclude evenness via the factor 2.
        have : Even (2 * padicValNat q d) := even_two_mul _
        simp [hpow]
      -- Translate evenness of the sum into evenness of the first addend.
      have h_even_sum :
          Even (padicValNat q n.natAbs + padicValNat q (d ^ 2)) := by
        simpa [h_val] using h_even_prod_q
      -- Parity of a sum implies both summands have the same parity; use the evenness of the second.
      have h_parity := (Nat.even_add).mp h_even_sum
      exact h_parity.mpr h_even_dsq
  -- Step 5.3: Invoke the characterization to obtain the desired representation of `n.natAbs`.
  obtain ⟨aN, bN, h_sum_nat⟩ :=
    (Nat.eq_sq_add_sq_iff (n := n.natAbs)).2 h_even_n
  /- Step 6: Convert the natural-number witnesses back to integers
     and rewrite the target equality in ℤ. -/
  -- Step 6.1: Cast the equality `n.natAbs = aN^2 + bN^2` to ℤ.
  have h_sum_int : (n.natAbs : ℤ) = (aN ^ 2 : ℕ) + bN ^ 2 := by
    exact_mod_cast h_sum_nat
  -- Step 6.2: Replace `n.natAbs` by `n` using non‑negativity.
  have h_cast_natAbs : (n.natAbs : ℤ) = n := by
    -- For non‑negative integers, the absolute value equals the integer itself.
    have := abs_of_nonneg hn_nonneg
    simpa using this
  -- Step 6.3: Assemble the final integer witnesses.
  refine ⟨(aN : ℤ), (bN : ℤ), by
    -- Replace `(aN^2 : ℕ)` by `(aN : ℤ)^2`, and similarly for `bN`.
    have h_cast_sq : (aN : ℤ) ^ 2 + (bN : ℤ) ^ 2 = (aN ^ 2 : ℕ) + bN ^ 2 := by
      norm_cast
    -- Combine all the rewrites to conclude.
    calc
      (aN : ℤ) ^ 2 + (bN : ℤ) ^ 2
          = (aN ^ 2 : ℕ) + bN ^ 2 := by exact h_cast_sq
      _ = (n.natAbs : ℤ) := by exact h_sum_int.symm
      _ = n := h_cast_natAbs
    ⟩
