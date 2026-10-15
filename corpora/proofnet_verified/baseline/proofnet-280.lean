import Mathlib

open Real
open scoped BigOperators



/-Informal Statement

If $a$ is a nonzero integer, then for $n>m$ show that $\left(a^{2^{n}}+1, a^{2^{m}}+1\right)=1$ or 2 depending on whether $a$ is odd or even.
-/

/-Informal Proof

\begin{align*}
\operatorname{ord}_p\, n!  &= \sum_{k\geq 1} \left \lfloor \frac{n}{p^{k}}\right \rfloor \leq  \sum_{k\geq 1}  \frac{n}{p^{k}} = \frac{n}{p} \frac{1}{1 - \frac{1}{p}} = \frac{n}{p-1}
\end{align*}

The decomposition of $n!$ in prime factors is

$n! = p_1^{\alpha_1}p_2^{\alpha_2}\cdots p_k^{\alpha_k}$ 
where $\alpha_i = \operatorname{ord}_{p_i}\, n! \leq \frac{n}{p_i-1}$, and $p_i \leq n, \ i=1,2,\cdots,k$.

Then
\begin{align*}
n! &\leq p_1^{\frac{n}{p_1-1}}p_2^{\frac{n}{p_2-1}}\cdots p_k^{\frac{n}{p_n-1}}\\
\sqrt[n]{n!} &\leq p_1^{\frac{1}{p_1-1}}p_2^{\frac{1}{p_2-1}}\cdots p_k^{\frac{1}{p_n-1}}\\
&\leq \prod_{p\leq n} p^{\frac{1}{p-1}}
\end{align*}
(the values of $p$ in this product describe all prime numbers $p\leq n$.)
-/

theorem Ireland_Rosen_exercise_2_4 {a : ℤ} (_ha : a ≠ 0)
  (hf : f_a = λ n m : ℕ => Int.gcd (a^(2^n) + 1) (a^(2^m)+1)) {n m : ℕ}
  (hnm : n > m) :
  (Odd a → f_a n m = 2) ∧ (Even a → f_a n m = 1) := by
  classical
  -- Step 1: abbreviate the two numbers whose gcd we study.
  let x : ℤ := a^(2^n) + 1
  let y : ℤ := a^(2^m) + 1
  -- Step 2: unfold the given definition of `f_a n m` and name its value `d` (a natural number).
  have hf_eval : f_a n m = Int.gcd x y := by simp [hf, x, y]
  let d : ℕ := Int.gcd x y
  -- Step 3: basic gcd facts — `(d : ℤ)` divides the two inputs.
  have hdiv_left : (d : ℤ) ∣ x := by simpa [d] using (Int.gcd_dvd_left x y)
  have hdiv_right : (d : ℤ) ∣ y := by simpa [d] using (Int.gcd_dvd_right x y)
  -- Step 3.1: the same divisibilities viewed in `ℕ` via `natAbs`.
  have hdiv_left_nat : d ∣ x.natAbs := (Int.natCast_dvd).1 hdiv_left
  have hdiv_right_nat : d ∣ y.natAbs := (Int.natCast_dvd).1 hdiv_right
  -- Step 4: show `(d : ℤ)` divides `x^2 - 1`, hence also `a^(2^(m+1)) - 1`.
  have hdiv_pow : (d : ℤ) ∣ a^(2^(m + 1)) - 1 := by
    -- Step 4.1: `(d : ℤ)` divides `(a^(2^m)+1)*(a^(2^m)-1)` via `hdiv_right`.
    have hmul : (d : ℤ) ∣ (a^(2^m) + 1) * (a^(2^m) - 1) :=
      dvd_mul_of_dvd_left hdiv_right _
    -- Step 4.2: rewrite the product as a difference of squares.
    have hsq : (a^(2^m) + 1) * (a^(2^m) - 1) = (a^(2^m))^2 - 1 := by ring
    -- Step 4.3: identify `(a^(2^m))^2` with `a^(2^(m+1))`.
    have hpow : (a^(2^m))^2 = a^(2^(m + 1)) := by
      have htwo : (2^m : ℕ) * 2 = 2^(m + 1) := by
        have h := Nat.pow_succ 2 m
        exact h.symm
      calc
        (a^(2^m))^2 = a^((2^m) * 2) := by simpa using (pow_mul a (2^m) 2).symm
        _ = a^(2^(m + 1)) := by simp [htwo]
    -- Step 4.4: conclude the desired divisibility.
    have hmul_eq : (a^(2^m) + 1) * (a^(2^m) - 1) = a^(2^(m + 1)) - 1 := by
      calc
        (a^(2^m) + 1) * (a^(2^m) - 1) = (a^(2^m))^2 - 1 := hsq
        _ = a^(2^(m + 1)) - 1 := by simp [hpow]
    simpa [hmul_eq] using hmul
  -- Step 5: lift the divisor one power higher so that `(d : ℤ)` also divides `a^(2^n) - 1`.
  have hdiv_big : (d : ℤ) ∣ a^(2^n) - 1 := by
    -- Step 5.1: derive the congruence `a^(2^(m+1)) ≡ 1 [ZMOD d]`.
    have h_mod : a^(2^(m + 1)) ≡ 1 [ZMOD d] := (Int.modEq_iff_dvd).2 (by
      have := Int.dvd_neg.mpr hdiv_pow
      simpa [Int.sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this)
    -- Step 5.2: raise both sides to the power `2^(n-(m+1))`.
    have hm1 : m.succ ≤ n := Nat.succ_le_of_lt hnm
    have hpow_split : 2^n = 2^(m + 1) * 2^(n - (m + 1)) := by
      have hsum : (m + 1) + (n - (m + 1)) = n := Nat.add_sub_of_le hm1
      calc
        2^n = 2^((m + 1) + (n - (m + 1))) := by simp [hsum]
        _ = 2^(m + 1) * 2^(n - (m + 1)) := by simp [Nat.pow_add]
    have hpow_mod : a^(2^n) ≡ 1 [ZMOD d] := by
      have h := Int.ModEq.pow (2^(n - (m + 1))) h_mod
      have hrewrite :
          (a^(2^(m + 1)))^(2^(n - (m + 1))) = a^(2^n) := by
        calc
          (a^(2^(m + 1)))^(2^(n - (m + 1)))
              = a^(2^(m + 1) * 2^(n - (m + 1))) := by
                simpa using (pow_mul a (2^(m + 1)) (2^(n - (m + 1)))).symm
          _ = a^(2^n) := by simp [hpow_split]
      simpa [hrewrite] using h
    -- Step 5.3: turn the congruence into a divisibility of the difference.
    have hdiv_tmp : (d : ℤ) ∣ 1 - a^(2^n) := (Int.modEq_iff_dvd).1 hpow_mod
    have := Int.dvd_neg.mpr hdiv_tmp
    simpa [Int.sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  -- Step 6: `d` divides the difference of `x` and `a^(2^n) - 1`, which is `2`, so `(d : ℤ) ∣ 2`.
  have hdiv_two_int : (d : ℤ) ∣ 2 := by
    have hdiff : (d : ℤ) ∣ (a^(2^n) + 1) - (a^(2^n) - 1) := Int.dvd_sub hdiv_left hdiv_big
    have hdiff_simpl : (a^(2^n) + 1) - (a^(2^n) - 1) = 2 := by ring
    simpa [hdiff_simpl] using hdiff
  -- Step 6.1: convert that to a natural divisibility statement.
  have hdiv_two_nat : d ∣ 2 := (Int.natCast_dvd).1 hdiv_two_int
  -- Step 7: split by the parity of `a`.
  constructor
  · -- Odd `a` case: the gcd must be `2`.
    intro ha_odd
    -- Step 7.1: establish evenness of `x` and `y`.
    have hodd_pow_n : Odd (a^(2^n)) := ha_odd.pow
    have hodd_pow_m : Odd (a^(2^m)) := ha_odd.pow
    have hEven_left : Even x := by
      -- recall `x = a^(2^n) + 1`
      simpa [x] using hodd_pow_n.add_one
    have hEven_right : Even y := by
      simpa [y] using hodd_pow_m.add_one
    -- Step 7.2: therefore `2` divides both `x.natAbs` and `y.natAbs`, hence divides `d`.
    have htwo_left : 2 ∣ x.natAbs := by
      have hx_int : (2 : ℤ) ∣ x := hEven_left.two_dvd
      -- bridge `(2 : ℤ) ∣ x` to a natural divisibility on `x.natAbs`
      exact (Int.natCast_dvd).1 hx_int
    have htwo_right : 2 ∣ y.natAbs := by
      have hy_int : (2 : ℤ) ∣ y := hEven_right.two_dvd
      exact (Int.natCast_dvd).1 hy_int
    have htwo_div_d : 2 ∣ d := by
      have htmp := Nat.dvd_gcd htwo_left htwo_right
      -- `Int.gcd` is `Nat.gcd` on the absolute values.
      simpa [d, Int.gcd_eq_natAbs] using htmp
    -- Step 7.3: nat divisibility both ways forces `d = 2`.
    have hd_eq_two : d = 2 := by
      have := Nat.dvd_antisymm hdiv_two_nat htwo_div_d
      simpa using this
    -- Step 7.4: finish the odd case.
    have hfa_val : f_a n m = d := by simpa [d] using hf_eval
    simp [hfa_val, hd_eq_two]
  · -- Even `a` case: the gcd must be `1`.
    intro ha_even
    -- Step 7.5: powers of an even number (with positive exponent) remain even.
    have hne_n : (2^n : ℕ) ≠ 0 := pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)
    have hne_m : (2^m : ℕ) ≠ 0 := pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)
    have heven_pow_n : Even (a^(2^n)) := ha_even.pow_of_ne_zero hne_n
    have heven_pow_m : Even (a^(2^m)) := ha_even.pow_of_ne_zero hne_m
    -- Step 7.6: consequently `x` and `y` are odd.
    have hodd_left : Odd x := by
      simpa [x] using heven_pow_n.add_one
    have hodd_right : Odd y := by
      simpa [y] using heven_pow_m.add_one
    -- Step 7.7: if `2` divided `d`, it would divide `x`, contradicting oddness.
    have hnot_two_div_d : ¬ 2 ∣ d := by
      intro h2d
      have h2x_nat : 2 ∣ x.natAbs := Nat.dvd_trans h2d hdiv_left_nat
      rcases h2x_nat with ⟨t, ht⟩
      rcases (Int.natAbs_odd).2 hodd_left with ⟨k, hk⟩
      -- Now `x.natAbs = 2 * k + 1` (odd) and also `x.natAbs = 2 * t` (even).
      have hEq : 2 * k + 1 = 2 * t := by
        calc
          2 * k + 1 = x.natAbs := hk.symm
          _ = 2 * t := ht
      -- Reduce the equality modulo 2 to reach a contradiction.
      have hmod := congrArg (fun z => z % 2) hEq
      have hleft : (2 * k + 1) % 2 = 1 := by norm_num
      have hright : (2 * t) % 2 = 0 := by
        -- `2 * t` is obviously divisible by 2.
        have : 2 ∣ 2 * t := ⟨t, rfl⟩
        exact Nat.mod_eq_zero_of_dvd this
      -- The remainders `1` and `0` cannot be equal.
      exact by
        have := hmod
        simp [hleft, hright] at this
    -- Step 7.8: since `d ∣ 2` but `2 ∤ d`, the only possibility is `d = 1`.
    have hd_eq_one : d = 1 := by
      have hcases : d = 1 ∨ d = 2 := (Nat.dvd_prime Nat.prime_two).1 hdiv_two_nat
      cases hcases with
      | inl h => exact h
      | inr h =>
          -- the branch `d = 2` contradicts `hnot_two_div_d`
          have : 2 ∣ d := by simp [h]
          exact (hnot_two_div_d this).elim
    -- Step 7.9: finish the even case.
    have hfa_val : f_a n m = d := by simpa [d] using hf_eval
    simp [hfa_val, hd_eq_one]
