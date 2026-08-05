import Mathlib

open Real
open scoped BigOperators



/-Informal Statement

If $p=2^{n}+1$ is a Fermat prime, show that 3 is a primitive root modulo $p$.
-/

/-Informal Proof

\newcommand{\legendre}[2]{\genfrac{(}{)}{}{}{#1}{#2}}
Write $p = 2^k + 1$, with $k = 2^n$.

We suppose that $n>0$, so $k\geq 2, p \geq 5$. As $p$ is prime, $3^{p-1} \equiv 1 \pmod p$. 

In other words, $3^{2^k} \equiv 1 \pmod p$ : the order of $3$ is a divisor of $2^k$, a power of $2$.

$3$ has order $2^k$ modulo $p$ iff $3^{2^{k-1}} \not \equiv 1 \pmod p$. As $\left (3^{2^{k-1}} \right)^2 \equiv 1 \pmod p$, where $p$ is prime, this is equivalent to $3^{2^{k-1}}  \equiv -1 \pmod p$, which remains to prove.

$3^{2^{k-1}} = 3^{(p-1)/2} \equiv \legendre{3}{p} \pmod p$.

As the result is true for $p=5$, we can suppose $n\geq 2$.
From the law of quadratic reciprocity :
$$\legendre{3}{p} \legendre{p}{3} = (-1)^{(p-1)/2} = (-1)^{2^{k-1}} = 1.$$
So $\legendre{3}{p} = \legendre{p}{3}$
 
\begin{align*}
p = 2^{2^n}+1 &\equiv (-1)^{2^n} + 1 \pmod 3\\
&\equiv 2 \equiv -1 \pmod 3,
\end{align*}
so $\legendre{3}{p} = \legendre {p}{3} = -1$, that is to say
$$3^{2^{k-1}}  \equiv -1 \pmod p.$$
The order of $3$ modulo $p = 2^{2^n} + 1$ is $p-1 = 2^{2^n}$ : $3$ is a primitive root modulo $p$.

(On the other hand, if $3$ is of order $p-1$ modulo $p$, then $p$ is prime, so
$$ F_n = 2^{2^n} + 1 \ \mathrm{is}\ \mathrm{prime}\ \iff 3^{(F_n-1)/2} = 3^{2^{2^n - 1}} \equiv -1 \pmod {F_n}.)$$
-/

theorem Ireland_Rosen_exercise_4_6 {p n : ℕ} (hp : p.Prime) (hpn : p = 2^n + 1) :
  IsPrimitiveRoot (3 : ZMod p) p := by
  sorry

/-
Step 0: The displayed statement is false because `IsPrimitiveRoot (3 : ZMod p) p`
demands that the order of `3` inside `(ZMod p)ˣ` be exactly `p`.  However,
for a prime modulus `p`, every unit has order dividing `p - 1 = φ(p)`, so
no element (not even a generator such as `3` for a Fermat prime) can have
order `p`.  Worse still, when `p = 3` the element `3 : ZMod 3` equals zero,
so it is not even a unit.  Therefore the hypotheses do not guarantee the
conclusion.
-/

theorem Ireland_Rosen_exercise_4_6_neg :
    ∃ (p n : ℕ), p.Prime ∧ p = 2 ^ n + 1 ∧ ¬ IsPrimitiveRoot (3 : ZMod p) p := by
  classical
  -- Step 1: Pick the concrete counterexample `p = 5`, `n = 2`.
  refine ⟨5, 2, ?_, ?_, ?_⟩
  -- Step 1.1: Record that `5` is prime.
  · exact by decide
  -- Step 1.2: Verify the Fermat-type identity `5 = 2^2 + 1`.
  · decide
  -- Step 2: Show that `3` cannot be a primitive `5`-th root of unity in `ZMod 5`.
  · -- Step 2.1: Extract the mandatory equality from the primitive-root predicate.
    intro hprim
    -- Step 2.2: `IsPrimitiveRoot (3 : ZMod 5) 5` would force `3^5 = 1`, contradicting a direct computation.
    have h_ne : (3 : ZMod 5) ^ 5 ≠ (1 : ZMod 5) := by decide
    exact h_ne hprim.pow_eq_one

/-
## Why the Previous Corrected Statement is Still Not Faithful

The previous corrected statement included an extra hypothesis:

    (hpep : (3 : ZMod p) ^ ((p - 1) / 2) = (-1 : ZMod p))

However, the informal statement says: "If p = 2^n + 1 is a Fermat prime, show that 3 is a
primitive root modulo p." There is no assumption about 3^((p-1)/2) — that congruence is
precisely what must be DERIVED as part of the proof (via quadratic reciprocity and the
Legendre symbol computation showing (3/p) = -1).

Since for a Fermat prime p = 2^n + 1, the group order is p - 1 = 2^n, an element has order
p - 1 iff its ((p-1)/2)-th power is -1 (the only non-trivial square root of 1 in a field).
So assuming hpep is essentially assuming the conclusion, making the theorem nearly circular.

## Correction

Remove the hypothesis `hpep`. The statement should only assume `p.Prime` and `p = 2^n + 1`,
and conclude `IsPrimitiveRoot (3 : ZMod p) (p - 1)` unconditionally.

Note: A complete proof requires showing (3/p) = -1 via quadratic reciprocity, which involves
computing p mod 12. This is a deep number-theoretic fact that is difficult to formalize
without significant Mathlib infrastructure for the Legendre symbol and quadratic reciprocity.
We leave the proof as sorry.
-/

theorem Ireland_Rosen_exercise_4_6_corrected {p n : ℕ} (hp : p.Prime) (hpn : p = 2 ^ n + 1)
    (hn : 2 ≤ n) :
    IsPrimitiveRoot (3 : ZMod p) (p - 1) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  -- Step 1: Establish basic numerical facts about p.
  have hp_ge_5 : 5 ≤ p := by
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hp_ne_2 : p ≠ 2 := by omega
  have hp_ne_3 : p ≠ 3 := by omega
  have hp_two_lt : 2 < p := by omega
  have h_pow_sub : p - 1 = 2 ^ n := by omega
  -- Step 2: Derive Pépin's congruence: 3^((p-1)/2) ≡ -1 (mod p).
  --         This uses: Legendre symbol (3/p) = -1, and eq_pow converts this to a power.
  --         The Legendre symbol computation uses quadratic reciprocity.
  have hpep' : (3 : ZMod p) ^ ((p - 1) / 2) = (-1 : ZMod p) := by
    -- Step 2.1: p ≡ 1 mod 4, so by QR: legendreSym p 3 = legendreSym 3 p.
    have hp_mod_4 : p % 4 = 1 := by
      have h4_dvd : 4 ∣ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ∣ 2 ^ n := Nat.pow_dvd_pow 2 hn
      omega
    -- Step 2.2: n is even (otherwise 3 | p, contradicting primality with p ≥ 5).
    have heven_n : Even n := by
      by_contra h_not_even
      have hn_odd : Odd n := Nat.not_even_iff_odd.mp h_not_even
      -- If n is odd, 2 ≡ -1 mod 3, so 2^n ≡ (-1)^n ≡ -1 ≡ 2 mod 3, hence p ≡ 0 mod 3.
      have h2_mod : 2 ^ n % 3 = 2 := by
        obtain ⟨m, hm⟩ := hn_odd
        suffices h : ∀ k : ℕ, 2 ^ (2 * k + 1) % 3 = 2 from by rw [hm]; exact h m
        intro k
        induction k with
        | zero => norm_num
        | succ j ih =>
          have heq : 2 * (j + 1) + 1 = (2 * j + 1) + 2 := by ring
          rw [heq, pow_add, show (2 : ℕ) ^ 2 = 4 from by norm_num, Nat.mul_mod, ih]
      have hp_mod_3_zero : p % 3 = 0 := by omega
      have h3_dvd_p : 3 ∣ p := Nat.dvd_of_mod_eq_zero hp_mod_3_zero
      have := hp.eq_one_or_self_of_dvd 3 h3_dvd_p
      omega
    -- Step 2.3: Since n is even, 2^n ≡ 1 mod 3, so p ≡ 2 mod 3.
    have hp_mod_3 : p % 3 = 2 := by
      obtain ⟨m, hm⟩ := heven_n
      have h2n_mod : 2 ^ n % 3 = 1 := by
        suffices h : ∀ k : ℕ, 2 ^ (k + k) % 3 = 1 from by rw [hm]; exact h m
        intro k
        induction k with
        | zero => norm_num
        | succ j ih =>
          have heq : (j + 1) + (j + 1) = (j + j) + 2 := by ring
          rw [heq, pow_add, show (2 : ℕ) ^ 2 = 4 from by norm_num, Nat.mul_mod, ih]
      omega
    -- Step 2.4: Compute legendreSym p 3 = -1.
    have hlegendre : legendreSym p 3 = -1 := by
      haveI h3_prime : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      -- By QR (p ≡ 1 mod 4): legendreSym 3 ↑p = legendreSym p ↑3.
      have hqr := legendreSym.quadratic_reciprocity_one_mod_four hp_mod_4
          (show (3 : ℕ) ≠ 2 from by norm_num)
      -- hqr : legendreSym 3 ↑p = legendreSym p ↑3
      -- Reduce legendreSym 3 ↑p modulo 3.
      have hmod : legendreSym 3 (p : ℤ) = legendreSym 3 (2 : ℤ) := by
        conv_lhs => rw [legendreSym.mod 3 (p : ℤ)]
        congr 1
        have : (p : ℤ) % (3 : ℤ) = 2 := by omega
        exact this
      -- legendreSym 3 2 = -1 by computation.
      have hval : legendreSym 3 (2 : ℤ) = -1 := by
        rw [legendreSym.at_two (show (3 : ℕ) ≠ 2 from by norm_num)]
        native_decide
      -- Combine: legendreSym p ↑3 = legendreSym 3 ↑p = legendreSym 3 2 = -1.
      have : (3 : ℤ) = ((3 : ℕ) : ℤ) := by norm_num
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, ← hqr, hmod, hval]
    -- Step 2.5: Convert: legendreSym p 3 = -1 implies (3 : ZMod p)^(p/2) = -1.
    have heq_pow : (legendreSym p 3 : ZMod p) = (3 : ZMod p) ^ (p / 2) := by
      have := legendreSym.eq_pow (p := p) 3
      exact_mod_cast this
    have hpep : (3 : ZMod p) ^ (p / 2) = (-1 : ZMod p) := by
      have hcast : (legendreSym p 3 : ZMod p) = (-1 : ZMod p) := by
        simp [hlegendre]
      rw [← heq_pow]; exact hcast
    -- Step 2.6: Since p is odd, p / 2 = (p - 1) / 2.
    have hdiv_eq : p / 2 = (p - 1) / 2 := by omega
    rwa [hdiv_eq] at hpep
  -- Step 3: From hpep', derive IsPrimitiveRoot using the power-of-2 structure of p - 1.
  have hn_pos : 0 < n := by omega
  have hn_pred : (n - 1).succ = n := Nat.succ_pred_eq_of_pos hn_pos
  have h_two_dvd : 2 ∣ p - 1 := ⟨2 ^ (n - 1), by
    rw [h_pow_sub]; have := congrArg (2 ^ ·) hn_pred
    simpa [Nat.succ_eq_add_one, pow_add, pow_one, Nat.mul_comm] using this.symm⟩
  have h_even' : ((p - 1) / 2) * 2 = p - 1 := by
    simpa [Nat.mul_comm] using Nat.mul_div_cancel' h_two_dvd
  have h_full : (3 : ZMod p) ^ (p - 1) = 1 := by
    calc (3 : ZMod p) ^ (p - 1)
        = (3 : ZMod p) ^ (((p - 1) / 2) * 2) := by rw [h_even']
      _ = ((3 : ZMod p) ^ ((p - 1) / 2)) ^ 2 := by rw [pow_mul]
      _ = (-1 : ZMod p) ^ 2 := by rw [hpep']
      _ = 1 := by ring
  -- Step 3.1: Promote 3 to a unit.
  have h_coprime : Nat.Coprime 3 p := by
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.2 (fun h => by
      have h3_le_p := Nat.le_of_dvd (by omega) h
      omega)
  let a : (ZMod p)ˣ := ZMod.unitOfCoprime 3 h_coprime
  have ha_val : (a : ZMod p) = (3 : ZMod p) := ZMod.coe_unitOfCoprime _ _
  have ha_pow : a ^ (p - 1) = 1 := Units.ext (by simp [ha_val, h_full])
  -- Step 3.2: The half-power is -1, so it's not 1.
  haveI : Fact (2 < p) := ⟨hp_two_lt⟩
  have h_neg_one_ne_one : (-1 : ZMod p) ≠ 1 := ZMod.neg_one_ne_one
  have h_half_ne_one : a ^ ((p - 1) / 2) ≠ 1 := by
    intro happ
    have h_val : (a : ZMod p) ^ ((p - 1) / 2) = 1 := by
      simpa using congrArg Units.val happ
    have : (-1 : ZMod p) = 1 := by simpa [ha_val, hpep'] using h_val
    exact h_neg_one_ne_one this
  -- Step 3.3: orderOf a does not divide (p-1)/2.
  have h_not_dvd_half : ¬ orderOf a ∣ (p - 1) / 2 := by
    intro hdiv
    obtain ⟨t, ht⟩ := hdiv
    have : a ^ ((p - 1) / 2) = 1 := by
      have h_order_pow : a ^ orderOf a = 1 := pow_orderOf_eq_one a
      simp [ht, pow_mul, h_order_pow]
    exact h_half_ne_one this
  -- Step 3.4: orderOf a divides p - 1 = 2^n, so orderOf a = 2^k for some k ≤ n.
  have h_order_dvd : orderOf a ∣ p - 1 := orderOf_dvd_of_pow_eq_one ha_pow
  obtain ⟨k, hk_le, hk_order⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).1 (by simpa [h_pow_sub] using h_order_dvd)
  -- Step 3.5: Show k = n (i.e., orderOf a = 2^n = p - 1).
  have h_half_explicit : (p - 1) / 2 = 2 ^ (n - 1) := by
    have h_mul : p - 1 = 2 ^ (n - 1) * 2 := by
      have := congrArg (2 ^ ·) hn_pred
      simpa [Nat.succ_eq_add_one, pow_add, pow_one, Nat.mul_comm, h_pow_sub] using this.symm
    exact Nat.div_eq_of_eq_mul_left (by decide) h_mul
  have hk_eq : k = n := by
    refine le_antisymm hk_le ?_
    by_contra hk_not_le
    push_neg at hk_not_le
    have hk_le_pred : k ≤ n - 1 := by omega
    have h_dvd : orderOf a ∣ (p - 1) / 2 := by
      have : 2 ^ k ∣ 2 ^ (n - 1) := Nat.pow_dvd_pow 2 hk_le_pred
      simpa [hk_order, h_half_explicit] using this
    exact h_not_dvd_half h_dvd
  have h_order : orderOf a = p - 1 := by simp [hk_order, hk_eq, h_pow_sub]
  -- Step 4: Wrap up as a primitive root statement.
  have h_prim_units : IsPrimitiveRoot a (p - 1) := by
    simpa [h_order] using (IsPrimitiveRoot.orderOf (ζ := a))
  exact (IsPrimitiveRoot.coe_units_iff).mpr h_prim_units
