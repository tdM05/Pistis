import Mathlib

open Real
open scoped BigOperators



/-Informal Statement

Show that any prime divisor of $x^{4}-x^{2}+1$ is congruent to 1 modulo 12 .
-/

/-Informal Proof

\newcommand{\legendre}[2]{\genfrac{(}{)}{}{}{#1}{#2}}
$\bullet$ As $a^6 +1 = (a^2+1)(a^4-a^2+1)$, $p\mid a^4 - a^2+1$ implies $p \mid a^6 + 1$, so $\legendre{-1}{p} = 1$ and $p\equiv 1 \pmod 4$.

$\bullet$ $p \mid 4a^4 - 4 a^2 +4 = (2a-1)^2 + 3$, so $\legendre{-3}{p} = 1$.

As $-3 \equiv 1 \pmod 4$, $\legendre{-3}{p} = \legendre{p}{3}$, so $\legendre{p}{3} = 1$, thus $p \equiv 1 \pmod 3$.

$4 \mid p-1$ and $3 \mid p-1$, thus $12 \mid p-1$ : $$p \equiv 1 \pmod {12}.$$
-/

theorem Ireland_Rosen_exercise_5_13 {p x: ℤ} (hp : Prime p)
  (hpx : p ∣ (x^4 - x^2 + 1)) : p ≡ 1 [ZMOD 12] := by
  sorry

/-
The original statement is false as written because `Prime p` in `ℤ` allows negative primes.
For instance, `p = -13` is prime in the Lean sense (its absolute value is the usual prime `13`),
and `-13` divides `2^4 - 2^2 + 1 = 13`, but `-13 ≡ 11 [ZMOD 12] ≠ 1`.
The corrected statement needs the additional premise that the prime divisor is the usual
positive natural prime (or, equivalently, that `p > 0`).
-/

theorem Ireland_Rosen_exercise_5_13_neg :
    ¬ (∀ p x : ℤ, Prime p → p ∣ (x^4 - x^2 + 1) → p ≡ 1 [ZMOD 12]) := by
  -- Step 1: Fix the explicit counterexample `p = -13`, `x = 2`.
  intro h
  -- Step 2: Register that `-13` is prime in `ℤ` (its absolute value is the natural prime `13`).
  have hprime : Prime (-13 : ℤ) := by
    -- Step 2.1: `13` is prime in `ℕ`.
    have hnat : Nat.Prime 13 := by decide
    -- Step 2.2: Transfer primality through `natAbs`.
    simpa [Int.prime_iff_natAbs_prime] using hnat
  -- Step 3: Show that `-13` divides `2^4 - 2^2 + 1 = 13`.
  have hdiv : (-13 : ℤ) ∣ (2 ^ 4 - 2 ^ 2 + 1) := by
    -- Step 3.1: Compute the value and exhibit the witness `-1`.
    refine ⟨-1, by norm_num⟩
  -- Step 4: Invoke the claimed statement to obtain the (incorrect) congruence.
  have hcong := h (-13) 2 hprime hdiv
  -- Step 5: But `-13` is not congruent to `1` modulo `12`.
  have hfail : ¬ ((-13 : ℤ) ≡ 1 [ZMOD 12]) := by decide
  -- Step 6: Contradiction with the claimed universal statement.
  exact hfail hcong

/-
Corrected version: work with a genuine natural prime `p : ℕ` (hence positive).
No need to assume `p ≠ 2` or `p ≠ 3` as extra hypotheses: the small primes `2` and
`3` never divide `x^4 - x^2 + 1` (the polynomial is identically `1` in both
`ZMod 2` and `ZMod 3`), so the divisibility hypothesis is impossible for them.
We dispatch those two cases by contradiction at the start of the proof, then run
the substantive `p ≥ 5` argument.
-/

theorem Ireland_Rosen_exercise_5_13_corrected {p : ℕ} {x : ℤ}
    (hp : Nat.Prime p)
    (hpx : (p : ℤ) ∣ (x^4 - x^2 + 1)) : (p : ℤ) ≡ 1 [ZMOD 12] := by
  -- Step 0: Dispose of `p = 2` and `p = 3` by showing the hypothesis is impossible.
  -- Step 0.1: For `p = 2`, the polynomial reduces to `1` in `ZMod 2`, so 2 cannot divide it.
  rcases eq_or_ne p 2 with rfl | hp2
  · exfalso
    have h_zero : ((x ^ 4 - x ^ 2 + 1 : ℤ) : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr hpx
    have h_one : ((x ^ 4 - x ^ 2 + 1 : ℤ) : ZMod 2) = 1 := by
      have h : ∀ y : ZMod 2, y ^ 4 - y ^ 2 + 1 = 1 := by decide
      push_cast
      exact h _
    have : (0 : ZMod 2) = 1 := h_zero ▸ h_one
    exact absurd this (by decide)
  -- Step 0.2: For `p = 3`, the polynomial again reduces to `1` in `ZMod 3`.
  rcases eq_or_ne p 3 with rfl | hp3
  · exfalso
    have h_zero : ((x ^ 4 - x ^ 2 + 1 : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hpx
    have h_one : ((x ^ 4 - x ^ 2 + 1 : ℤ) : ZMod 3) = 1 := by
      have h : ∀ y : ZMod 3, y ^ 4 - y ^ 2 + 1 = 1 := by decide
      push_cast
      exact h _
    have : (0 : ZMod 3) = 1 := h_zero ▸ h_one
    exact absurd this (by decide)
  -- Step 1: Now `p ≥ 5`. Work in `ZMod p`.
  haveI : Fact p.Prime := ⟨hp⟩
  let a : ZMod p := (x : ZMod p)
  -- Step 2.1: Record the polynomial vanishing modulo `p`.
  have hpoly : a ^ 4 - a ^ 2 + 1 = (0 : ZMod p) := by
    have hcast : ((x ^ 4 - x ^ 2 + 1 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (a := x ^ 4 - x ^ 2 + 1) (b := p)).2 hpx
    simpa [a] using hcast
  -- Step 2.2: Show `a ≠ 0`; otherwise the polynomial would equal `1`.
  have ha_ne_zero : a ≠ (0 : ZMod p) := by
    intro hzero
    have hcontr : (1 : ZMod p) = 0 := by simp [hzero] at hpoly
    exact one_ne_zero hcontr
  -- Step 3: Derive `a^6 = -1` from the factorization `(a^2+1)(a^4 - a^2 +1) = a^6 + 1`.
  have hpow6 : a ^ 6 = (-1 : ZMod p) := by
    have hfact : (a ^ 2 + 1) * (a ^ 4 - a ^ 2 + 1) = (0 : ZMod p) := by simp [hpoly]
    have hsum : a ^ 6 + 1 = (0 : ZMod p) := by
      calc
        a ^ 6 + 1 = (a ^ 2 + 1) * (a ^ 4 - a ^ 2 + 1) := by ring
        _ = 0 := hfact
    exact eq_neg_of_add_eq_zero_left hsum
  -- Step 3.1: Square to obtain `a^12 = 1`.
  have hpow12 : a ^ 12 = (1 : ZMod p) := by
    calc
      a ^ 12 = (a ^ 6) ^ 2 := by ring
      _ = (-1 : ZMod p) ^ 2 := by simp [hpow6]
      _ = 1 := by norm_num
  -- Step 4: `-1 ≠ 1` in this field because `p ≠ 2`.
  have hneg_ne_one : (-1 : ZMod p) ≠ 1 := by
    intro h
    have htwo_zero : (2 : ZMod p) = 0 := by
      calc
        (2 : ZMod p) = (1 : ZMod p) + 1 := by norm_num
        _ = (-1 : ZMod p) + 1 := by simp [h]
        _ = 0 := by abel
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff (a := 2) (b := p)).1 htwo_zero
    have hp_le : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hdiv
    have hp_ge : 2 ≤ p := hp.two_le
    have hp_eq : p = 2 := le_antisymm hp_le hp_ge
    exact hp2 hp_eq
  -- Step 5: `orderOf a` divides `12` (from `a^12 = 1`) but does not divide `6`.
  have horder_div12 : orderOf a ∣ 12 :=
    orderOf_dvd_of_pow_eq_one (x := a) (n := 12) hpow12
  have hpow6_ne_one : a ^ 6 ≠ (1 : ZMod p) := by
    intro h
    have : (-1 : ZMod p) = 1 := by
      calc
        (-1 : ZMod p) = a ^ 6 := hpow6.symm
        _ = 1 := h
    exact hneg_ne_one this
  have hnot_div6 : ¬ orderOf a ∣ 6 := by
    intro hdiv
    have : a ^ 6 = (1 : ZMod p) :=
      (orderOf_dvd_iff_pow_eq_one (x := a) (n := 6)).1 hdiv
    exact hpow6_ne_one this
  -- Step 6: Exclude the case `orderOf a = 4` via the original polynomial.
  have hnot_order4 : orderOf a ≠ 4 := by
    intro h4
    have hpow4 : a ^ 4 = (1 : ZMod p) := by simpa [h4] using pow_orderOf_eq_one a
    have hsq : a ^ 2 = (-1 : ZMod p) := by
      have h6' : a ^ 4 * a ^ 2 = (-1 : ZMod p) := by
        have := hpow6
        -- rewrite the left-hand side of `hpow6` as `a^4 * a^2`
        have h' : a ^ 6 = a ^ 4 * a ^ 2 := by simpa using (pow_add a 4 2)
        simpa [h'] using this
      have h6'' : (1 : ZMod p) * a ^ 2 = (-1 : ZMod p) := by
        simpa [hpow4] using h6'
      simpa using h6''
    have hthree : (3 : ZMod p) = 0 := by
      have h := hpoly
      calc
        (3 : ZMod p) = (1 : ZMod p) + 1 + 1 := by norm_num
        _ = a ^ 4 - a ^ 2 + 1 := by
          simp [hpow4, hsq, sub_eq_add_neg, add_comm]
        _ = 0 := h
    have hdiv3 : p ∣ 3 := (ZMod.natCast_eq_zero_iff (a := 3) (b := p)).1 hthree
    have hp_le : p ≤ 3 := Nat.le_of_dvd (by decide : 0 < 3) hdiv3
    have hp_ge : 3 ≤ p := by
      have hgt2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
      exact Nat.succ_le_of_lt hgt2
    have hp_eq : p = 3 := le_antisymm hp_le hp_ge
    exact hp3 hp_eq
  -- Step 7: From the possible divisors of `12`, only `12` survives.
  have horder_eq12 : orderOf a = 12 := by
    -- Step 7.1: Enumerate the divisors of `12`.
    have hmem : orderOf a ∈ Nat.divisors 12 :=
      (Nat.mem_divisors.mpr ⟨horder_div12, by decide⟩)
    have hlist : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by decide
    have hcases :
        orderOf a = 1 ∨ orderOf a = 2 ∨ orderOf a = 3 ∨
          orderOf a = 4 ∨ orderOf a = 6 ∨ orderOf a = 12 := by
      simpa [hlist, Finset.mem_insert, Finset.mem_singleton] using hmem
    -- Step 7.2: Rule out every option except `12`.
    rcases hcases with h1 | h2 | h3 | h4 | h6 | h12
    · have : orderOf a ∣ 6 := by simp [h1]
      exact (hnot_div6 this).elim
    · have : orderOf a ∣ 6 := by simp [h2]
      exact (hnot_div6 this).elim
    · have : orderOf a ∣ 6 := by simp [h3]
      exact (hnot_div6 this).elim
    · exact (hnot_order4 h4).elim
    · exact (hnot_div6 (by simp [h6])).elim
    · exact h12
  -- Step 8: Fermat's little theorem gives `orderOf a ∣ p - 1`.
  have hpow_card : a ^ (p - 1) = (1 : ZMod p) :=
    ZMod.pow_card_sub_one_eq_one (a := a) ha_ne_zero
  have horder_div_p1 : orderOf a ∣ p - 1 :=
    (orderOf_dvd_iff_pow_eq_one (x := a) (n := p - 1)).2 hpow_card
  -- Step 9: Combine with `orderOf a = 12` to get `12 ∣ p - 1`.
  have hdiv12 : 12 ∣ p - 1 := by simpa [horder_eq12] using horder_div_p1
  -- Step 10: Convert the divisibility to a congruence modulo `12`.
  have hnat_mod' : 1 ≡ p [MOD 12] :=
    (Nat.modEq_iff_dvd' (by exact hp.one_lt.le)).2 hdiv12
  have hnat_mod : p ≡ 1 [MOD 12] := hnat_mod'.symm
  -- Step 11: Lift the congruence to integers and conclude.
  have hmod : (p : ℤ) ≡ 1 [ZMOD 12] := (Int.natCast_modEq_iff).2 hnat_mod
  exact hmod
