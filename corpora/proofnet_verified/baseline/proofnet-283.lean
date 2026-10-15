import Mathlib

open Real
open scoped BigOperators


/--
This technical lemma isolates two distinct factors in the factorial product so that we can
force a desired divisor `N`.  It will be used repeatedly in the main argument.
-/
private lemma dvd_factorial_from_two_factors {N a b : ℕ}
    (hN : 1 ≤ N) (ha_pos : 1 ≤ a) (ha_lt : a < N)
    (hb_pos : 1 ≤ b) (hb_lt : b < N)
    (hneq : a ≠ b) (hdiv : N ∣ a * b) :
    N ∣ Nat.factorial (N - 1) := by
  classical
  -- Step 1: rewrite the factorial as a product over the interval `[1, N)` so it is easy
  -- to remove concrete factors.
  have hfact : Nat.factorial (N - 1) = ∏ x ∈ Finset.Ico 1 N, x := by
    simpa [Nat.sub_add_cancel hN, Nat.succ_eq_add_one]
      using (Finset.prod_Ico_id_eq_factorial (N - 1)).symm
  -- Step 2: record that `a` and `b` live inside this interval.
  set s := Finset.Ico 1 N with hs_def
  have ha_mem : a ∈ s := by
    simpa [s] using Finset.mem_Ico.mpr ⟨ha_pos, ha_lt⟩
  have hb_mem : b ∈ s := by
    simpa [s] using Finset.mem_Ico.mpr ⟨hb_pos, hb_lt⟩
  have hb_mem' : b ∈ s.erase a := by
    refine Finset.mem_erase.mpr ?_
    exact ⟨hneq.symm, hb_mem⟩
  -- Step 3: successively peel `a` and `b` from the product and record the remaining factor.
  have hprod :
      ∏ x ∈ s, x = a * b * ∏ x ∈ (s.erase a).erase b, x := by
    calc
      ∏ x ∈ s, x
          = a * ∏ x ∈ s.erase a, x := by
              simpa using (Finset.mul_prod_erase s (fun x => x) ha_mem).symm
      _ = a * (b * ∏ x ∈ (s.erase a).erase b, x) := by
              simpa [mul_comm, mul_assoc]
                using congrArg (fun t => a * t)
                  (Finset.mul_prod_erase (s.erase a) (fun x => x) hb_mem').symm
      _ = a * b * ∏ x ∈ (s.erase a).erase b, x := by
              simp [mul_assoc]
  -- Step 4: translate the previous identity into the desired divisibility statement.
  set rest := ∏ x ∈ (s.erase a).erase b, x with hrest_def
  have hfact' : Nat.factorial (N - 1) = (a * b) * rest := by
    have : ∏ x ∈ s, x = a * b * rest := by simpa [rest] using hprod
    simpa [this] using hfact
  obtain ⟨k, hk⟩ := hdiv
  have hmul : N ∣ (a * b) * rest := by
    refine ⟨k * rest, ?_⟩
    simp [hk, mul_assoc]
  simpa [hfact'] using hmul


/-Informal Statement

If $n$ is not a prime, show that $(n-1) ! \equiv 0(n)$, except when $n=4$.
-/

/-Informal Proof

Suppose that $n >1$ is not a prime. Then $n = uv$, where $2 \leq u \leq v \leq n-1$.

$\bullet$ If $u \neq v$, then $n = uv \mid (n-1)! = 1\times 2 \times\cdots \times u \times\cdots \times v \times \cdots \times (n-1)$ (even if $u\wedge v \neq 1$ !).

$\bullet$ If $u=v$, $n = u^2$ is a square.

If $u$ is not prime, $u =st,\ 2\leq s \leq t \leq u-1 \leq n-1$, and $n = u' v'$, where $u' =s,v' =st^2$ verify  $2 \leq u' < v' \leq n-1$. As in the first case, $n = u'v' \mid (n-1)!$.  

If $u = p$ is a prime, then $n =p^2$.

In the case $p = 2$, $n = 4$ and $n=4  \nmid (n-1)! = 6$. In the other case $p >2$, and $(n-1)! = (p^2 - 1)!$ contains the factors $p < 2p < p^2$, so $p^2 \mid (p^2-1)!, n \mid (n-1)!$.

Conclusion : if $n$ is not a prime, $(n - 1)! \equiv 0 \pmod n$, except when $n=4$.
-/

theorem Ireland_Rosen_exercise_3_10 {n : ℕ+} (hn0 : ¬ n.Prime) :
  Nat.factorial (n-1) ≡ 0 [MOD n] ↔ n ≠ 4 := by
  classical
  -- Step 0: package the underlying natural number once and for all.
  set N : ℕ := (n : ℕ) with hNdef
  have hNpos : 0 < N := n.pos
  have hNge1 : 1 ≤ N := Nat.succ_le_of_lt hNpos
  have hnNat : ¬ Nat.Prime N := by simpa [N] using hn0
  constructor
  · -- Step 1: assume the modular statement and deduce that `n ≠ 4`.
    intro hmod
    -- Step 1.1: show that equality with `4` contradicts the congruence directly.
    refine ?_
    intro h4
    have hN4 : N = 4 := by
      simpa [N] using congrArg Subtype.val h4
    have hmod4 : Nat.factorial 3 ≡ 0 [MOD (4 : ℕ)] := by
      simpa [N, hN4, h4] using hmod
    have hno : ¬ Nat.factorial 3 ≡ 0 [MOD (4 : ℕ)] := by decide
    exact hno hmod4
  · -- Step 2: assume `n ≠ 4` and prove the congruence directly.
    intro hn4
    -- Step 2.1: rewrite the hypothesis for the underlying natural number.
    have hnNat_ne4 : N ≠ 4 := by
      intro hN4
      apply hn4
      have : (n : ℕ) = 4 := by simpa [N] using hN4
      refine Subtype.ext ?_
      simpa [N] using this
    -- Step 2.2: the case `N = 1` is immediate.
    by_cases hN1 : N = 1
    · -- Step 2.2.1: `0! = 1`, so the congruence is automatic.
      have hdiv : N ∣ Nat.factorial (N - 1) := by
        have : (1 : ℕ) ∣ 1 := by simp
        simp [N, hN1]
      exact (Nat.modEq_zero_iff_dvd.mpr hdiv)
    · -- Step 2.2.2: now `N ≥ 2`, so we perform the full composite analysis.
      have hNgt1 : 1 < N := lt_of_le_of_ne hNge1 (by symm; exact hN1)
      have hNge2 : 2 ≤ N := Nat.succ_le_of_lt hNgt1
      -- Step 2.2.2.1: extract a non-trivial divisor of `N`.
      obtain ⟨u, hu_dvd, hu_ge2, hu_ltN⟩ := Nat.exists_dvd_of_not_prime2 hNge2 hnNat
      set v := N / u with hv_def
      have huv_mul : u * v = N := Nat.mul_div_cancel' hu_dvd
      have hdiv_uv : N ∣ u * v := by simp [huv_mul]
      -- Step 2.2.2.2: basic inequalities for the extracted factors.
      have ha_pos : 1 ≤ u := (by decide : 1 ≤ 2).trans hu_ge2
      have hu_gt1 : 1 < u := lt_of_lt_of_le (by decide : 1 < 2) hu_ge2
      have hu_pos : 0 < u := lt_trans zero_lt_one hu_gt1
      have hv_ne_zero : v ≠ 0 := by
        intro hvzero
        have : N = 0 := by simpa [v, hvzero] using huv_mul.symm
        exact (ne_of_gt hNpos) this
      have hv_pos : 0 < v := Nat.pos_of_ne_zero hv_ne_zero
      have hb_pos : 1 ≤ v := Nat.succ_le_of_lt hv_pos
      have hv_ltN : v < N := by
        simpa [v] using Nat.div_lt_self hNpos hu_gt1
      -- Step 2.2.2.3: split according to whether `u` and `v` coincide.
      have hdiv_goal : N ∣ Nat.factorial (N - 1) := by
        by_cases hsq : u = v
        · -- Step 2.2.2.3(a): the square case needs a refined sub-analysis.
          have hw_mul : N = u * u := by simpa [hsq] using huv_mul.symm
          have htwo_le_u : 2 ≤ u := hu_ge2
          -- Step 2.2.2.3(a)(i): `u` prime ⇒ use the `p` and `2p` trick (unless this is the forbidden `p = 2`).
          by_cases hw_prime : Nat.Prime u
          · -- Step 2.2.2.3(a)(i.1): rule out `u = 2`, otherwise we contradict `n ≠ 4`.
            have hw_ne2 : u ≠ 2 := by
              intro h2
              have hN4 : N = 4 := by simp [hw_mul, h2]
              exact hnNat_ne4 hN4
            have hw_gt2 : 2 < u := lt_of_le_of_ne htwo_le_u (by symm; exact hw_ne2)
            have hw_ge3 : 3 ≤ u := Nat.succ_le_of_lt hw_gt2
            have hw_gt1 : 1 < u := lt_of_lt_of_le (by decide : 1 < 3) hw_ge3
            have hw_pos : 0 < u := lt_trans zero_lt_one hw_gt1
            set b := 2 * u
            have hb_pos0 : 0 < b := Nat.mul_pos (by decide : 0 < 2) hw_pos
            have hb_pos' : 1 ≤ b := Nat.succ_le_of_lt hb_pos0
            have ha_lt : u < N := by
              have := lt_mul_of_one_lt_right hw_pos hw_gt1
              simpa [hw_mul, mul_comm] using this
            have hb_lt : b < N := by
              have := Nat.mul_lt_mul_of_pos_left hw_gt2 hw_pos
              have : 2 * u < u * u := by simpa [mul_comm] using this
              simpa [b, hw_mul, mul_comm] using this
            have ha_ne_b : u ≠ b := by
              have : u < b := by
                have := lt_mul_of_one_lt_right hw_pos (by decide : 1 < 2)
                simpa [b, mul_comm] using this
              exact ne_of_lt this
            have hab_div : N ∣ u * b := by
              refine ⟨2, ?_⟩
              simp [b, hw_mul, mul_comm, mul_assoc]
            exact dvd_factorial_from_two_factors hNge1 ha_pos ha_lt hb_pos' hb_lt ha_ne_b hab_div
          · -- Step 2.2.2.3(a)(ii): `u` composite ⇒ extract new factors strictly below `N`.
            obtain ⟨s, hs_dvd, hs_ge2, hs_lt⟩ := Nat.exists_dvd_of_not_prime2 htwo_le_u hw_prime
            set t := u / s with ht_def
            have hst_mul : s * t = u := Nat.mul_div_cancel' hs_dvd
            have hs_pos : 0 < s := lt_of_lt_of_le zero_lt_two hs_ge2
            have ht_ne_zero : t ≠ 0 := by
              intro ht0
              have : 0 = u := by simpa [t, ht0, mul_comm] using hst_mul
              exact (ne_of_gt hu_pos) this.symm
            have ht_pos : 0 < t := Nat.pos_of_ne_zero ht_ne_zero
            have ht_ne_one : t ≠ 1 := by
              intro ht1
              have : s = u := by simpa [t, ht1, mul_comm] using hst_mul
              exact (lt_irrefl _ (this.symm ▸ hs_lt))
            have ht_gt1 : 1 < t := lt_of_le_of_ne (Nat.succ_le_of_lt ht_pos) (by symm; exact ht_ne_one)
            have ht_ge2 : 2 ≤ t := Nat.succ_le_of_lt ht_gt1
            have htwle : 2 * t ≤ u := by
              have := Nat.mul_le_mul_right t hs_ge2
              simpa [two_mul, add_comm, add_left_comm, hst_mul, mul_comm, mul_left_comm, mul_assoc]
                using this
            have ht_lt_double : t < 2 * t := by
              have := lt_mul_of_one_lt_right ht_pos (by decide : 1 < (2 : ℕ))
              simpa [two_mul, mul_comm] using this
            have ht_lt_u : t < u := lt_of_lt_of_le ht_lt_double htwle
            have hs_ltN : s < N := lt_trans hs_lt hu_ltN
            have hpos_s : 1 ≤ s := (by decide : 1 ≤ 2).trans hs_ge2
            let a := s
            let b := s * t ^ 2
            have hb_expr : b = t * u := by
              calc
                b = s * (t * t) := by
                  simp [b, pow_two]
                _ = (s * t) * t := by
                  simp [mul_comm, mul_left_comm]
                _ = u * t := by simp [hst_mul]
                _ = t * u := by simp [mul_comm]
            have hb_pos0 : 0 < b := by
              have ht_sq_pos : 0 < t ^ 2 := pow_pos ht_pos 2
              exact Nat.mul_pos hs_pos ht_sq_pos
            have hb_pos' : 1 ≤ b := Nat.succ_le_of_lt hb_pos0
            have htsq_ge4 : 4 ≤ t ^ 2 := by
              have := Nat.mul_le_mul ht_ge2 ht_ge2
              simpa [pow_two, two_mul, add_comm, add_left_comm, add_assoc] using this
            have htsq_gt1 : 1 < t ^ 2 := lt_of_lt_of_le (by decide : 1 < 4) htsq_ge4
            have ha_ne_b : a ≠ b := by
              have : a < b := by
                have := lt_mul_of_one_lt_right hs_pos htsq_gt1
                simpa [a, b] using this
              exact ne_of_lt this
            have hb_ltN : b < N := by
              have := Nat.mul_lt_mul_of_pos_right ht_lt_u hu_pos
              simpa [hb_expr, hw_mul, mul_comm, mul_left_comm, mul_assoc] using this
            have hab_div : N ∣ a * b := by
              have hsq1 : a * b = (s * t) * (s * t) := by
                simp [a, b, pow_two, mul_comm, mul_left_comm]
              have hsq2 : a * b = u * u := by simpa [hst_mul] using hsq1
              have hsq3 : a * b = N := by simpa [hw_mul] using hsq2
              simp [hsq3]
            exact dvd_factorial_from_two_factors hNge1 hpos_s hs_ltN hb_pos' hb_ltN ha_ne_b hab_div
        · -- Step 2.2.2.3(b): the easy case `u ≠ v` corresponds directly to the informal proof.
          have hneq : u ≠ v := hsq
          exact dvd_factorial_from_two_factors hNge1 ha_pos hu_ltN hb_pos hv_ltN hneq hdiv_uv
      -- Step 2.2.2.4: translate the final divisibility back to the targeted congruence.
      exact (Nat.modEq_zero_iff_dvd.mpr hdiv_goal)
