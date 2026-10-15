import Mathlib

open Real
open scoped BigOperators



/-Informal Statement

Let $p$ and $q$ be distinct odd primes such that $p-1$ divides $q-1$. If $(n, p q)=1$, show that $n^{q-1} \equiv 1(p q)$.
-/

/-Informal Proof

As $n \wedge pq = 1, n\wedge p=1, n \wedge q = 1$, so from Fermat's Little Theorem
$$n^{q-1} \equiv 1 \pmod q,\qquad n^{p-1} \equiv 1 \pmod p.$$
$p-1 \mid q-1$, so there exists $k \in \mathbb{Z}$ such that $q-1 = k(p-1)$.
Thus
$$n^{q-1} = (n^{p-1})^k \equiv 1 \pmod p.$$
$p \mid n^{q-1} - 1, q \mid n^{q-1} - 1$, and $p\wedge q = 1$, so $pq \mid n^{q-1} - 1$ :
$$n^{q-1} \equiv 1 \pmod{pq}.$$
-/

theorem Ireland_Rosen_exercise_3_14 {p q n : ℕ} (hp0 : p.Prime ∧ p > 2)
  (hq0 : q.Prime ∧ q > 2) (hpq0 : p ≠ q) (hpq1 : p - 1 ∣ q - 1)
  (hn : n.gcd (p*q) = 1) :
  n^(q-1) ≡ 1 [MOD p*q] := by
  -- Step 1: extract the primality information for `p` and `q` so that we can use prime-specific lemmas.
  obtain ⟨hp, hp_gt_two⟩ := hp0
  obtain ⟨hq, hq_gt_two⟩ := hq0
  -- Step 2: show that `n` is coprime to `p` using the gcd hypothesis.
  have hcop_np : Nat.Coprime n p := by
    -- Step 2.1: prove that `p` cannot divide `n`, otherwise the gcd with `p * q` would not be `1`.
    have hp_not_dvd_n : ¬ p ∣ n := by
      intro hp_dvd_n
      -- Step 2.1.1: `p` divides `p * q`, hence it divides the gcd as well, contradicting `hn`.
      have hp_dvd_pq : p ∣ p * q := by
        -- Step 2.1.1.1: use the trivial divisibility `p ∣ p` to lift it to `p ∣ p * q`.
        exact dvd_mul_of_dvd_left (Nat.dvd_refl p) q
      have hp_dvd_gcd : p ∣ Nat.gcd n (p * q) :=
        Nat.dvd_gcd hp_dvd_n hp_dvd_pq
      -- Step 2.1.1.2: deduce `p ∣ 1`, contradicting primality.
      have : p ∣ 1 := by simpa [hn] using hp_dvd_gcd
      exact hp.not_dvd_one this
    -- Step 2.2: convert the non-divisibility into coprimality with the prime-specific lemma.
    have hprime_coprime : Nat.Coprime p n :=
      (hp.coprime_iff_not_dvd).2 hp_not_dvd_n
    simpa [Nat.coprime_comm] using hprime_coprime
  -- Step 3: repeat the gcd argument to obtain that `n` is coprime to `q`.
  have hcop_nq : Nat.Coprime n q := by
    -- Step 3.1: demonstrate that `q` does not divide `n`.
    have hq_not_dvd_n : ¬ q ∣ n := by
      intro hq_dvd_n
      -- Step 3.1.1: `q` divides `p * q`, so it divides the gcd, contradicting `hn` again.
      have hq_dvd_pq : q ∣ p * q := by
        -- Step 3.1.1.1: use the trivial divisibility `q ∣ q` to lift it to `q ∣ p * q`.
        exact dvd_mul_of_dvd_right (Nat.dvd_refl q) p
      have hq_dvd_gcd : q ∣ Nat.gcd n (p * q) :=
        Nat.dvd_gcd hq_dvd_n hq_dvd_pq
      -- Step 3.1.1.2: deduce the impossible conclusion `q ∣ 1`.
      have : q ∣ 1 := by simpa [hn, Nat.mul_comm] using hq_dvd_gcd
      exact hq.not_dvd_one this
    -- Step 3.2: translate `q ∤ n` into coprimality.
    have hprime_coprime : Nat.Coprime q n :=
      (hq.coprime_iff_not_dvd).2 hq_not_dvd_n
    simpa [Nat.coprime_comm] using hprime_coprime
  -- Step 4: establish that `p` and `q` themselves are coprime since they are distinct primes.
  have hcop_pq : Nat.Coprime p q := by
    -- Step 4.1: exclude the possibility that `p` divides `q`, which would force equality.
    have hp_not_dvd_q : ¬ p ∣ q := by
      intro hp_dvd_q
      -- Step 4.1.1: primality forces `p = q`, contradicting the distinctness hypothesis.
      have hp_eq_q : p = q :=
        (Nat.prime_dvd_prime_iff_eq hp hq).1 hp_dvd_q
      exact hpq0 hp_eq_q
    -- Step 4.2: convert the non-divisibility into coprimality.
    exact (hp.coprime_iff_not_dvd).2 hp_not_dvd_q
  -- Step 5: unpack the divisibility condition `(p - 1) ∣ (q - 1)` to obtain an explicit multiplier.
  obtain ⟨k, hk⟩ := hpq1
  -- Step 6: apply Fermat's little theorem (via Euler's totient theorem) to modulus `p`.
  have h_mod_p_base : n^(p - 1) ≡ 1 [MOD p] :=
    Nat.ModEq.pow_card_sub_one_eq_one hp hcop_np
  -- Step 6.1: raise the base congruence to the `k`th power so that the exponent becomes `q - 1`.
  have h_mod_p : n^(q - 1) ≡ 1 [MOD p] := by
    -- Step 6.1.1: move the exponent multiplication inside the congruence using `Nat.ModEq.pow`.
    have hpow := Nat.ModEq.pow (m := k) h_mod_p_base
    have hpow' : n^((p - 1) * k) ≡ 1 [MOD p] := by
      simpa [pow_mul] using hpow
    -- Step 6.1.2: rewrite the exponent with the equality produced by the divisibility hypothesis.
    simpa [hk] using hpow'
  -- Step 7: apply Fermat's little theorem directly to modulus `q`.
  have h_mod_q : n^(q - 1) ≡ 1 [MOD q] :=
    Nat.ModEq.pow_card_sub_one_eq_one hq hcop_nq
  -- Step 8: combine the congruences modulo `p` and modulo `q` using the Chinese Remainder Theorem for coprime moduli.
  have h_mod_pq :=
    (Nat.modEq_and_modEq_iff_modEq_mul hcop_pq).mp ⟨h_mod_p, h_mod_q⟩
  -- Step 9: conclude with the desired congruence modulo `p * q`.
  simpa [Nat.mul_comm] using h_mod_pq
