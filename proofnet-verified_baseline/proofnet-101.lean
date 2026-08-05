import Mathlib

open Real
open scoped BigOperators



/-Informal Statement

Let $p$ be an odd prime. Show that $a$ is a primitive root modulo $p$ iff $a^{(p-1) / q} \not \equiv 1(p)$ for all prime divisors $q$ of $p-1$.
-/

/-Informal Proof

$\bullet$ If $a$ is a primitive root, then $a^k \not \equiv 1$ for all $k, 1\leq k < p-1$, so $a^{(p-1)/q} \not \equiv 1 \pmod p$ for all prime divisors $q$ of $p - 1$.

$\bullet$ In the other direction, suppose $a^{(p-1)/q} \not \equiv 1 \pmod p$ for all prime divisors $q$ of $p - 1$.

Let $\delta$ the order of $a$, and $p-1 = q_1^{a_1}q_2^{a_2}\cdots q_k^{a_k}$ the decomposition of $p-1$ in prime factors. As $\delta \mid p-1, \delta = q_1^{b_1}p_2^{b_2}\cdots q_k^{b_k}$, with $b_i \leq a_i, i=1,2,\ldots,k$. If $b_i < a_i$ for some index $i$, then $\delta \mid (p-1)/q_i$, so $a^{(p-1)/q_i} \equiv 1 \pmod p$, which is in contradiction with the hypothesis. Thus $b_i = a_i$ for all $i$, and $\delta = q-1$ : $a$ is a primitive root modulo $p$.
-/

theorem Ireland_Rosen_exercise_4_8 {p : ℕ} {a : ZMod p} (hp : Odd p) (hp' : p.Prime) :
  IsPrimitiveRoot a p ↔ (∀ q : ℕ, q ∣ (p-1) → q.Prime → ¬ a^((p-1)/q) = 1) := by
  sorry

/-
Step 0: The displayed statement is false because `IsPrimitiveRoot a k`
demands that the order of `a` be exactly `k`.  For `a : ZMod p`, every unit
has order dividing `p - 1`, so no element can have order `p`.  Nevertheless,
actual primitive roots (elements whose order is `p - 1`) satisfy the
right-hand condition, so the equivalence fails for genuine primitive roots
such as `2` modulo `5`.
-/

theorem Ireland_Rosen_exercise_4_8_neg :
  ∃ (p : ℕ) (_hp : Odd p) (_hp' : p.Prime) (a : ZMod p),
      ¬ (IsPrimitiveRoot a p ↔
        (∀ q : ℕ, q ∣ (p - 1) → q.Prime → ¬ a ^ ((p - 1) / q) = 1)) := by
  classical
  -- Step 1: Choose the concrete counterexample `p = 5`, `a = 2`.
  refine ⟨5, by decide, by decide, (2 : ZMod 5), ?_⟩
  -- Step 2: Record that the right-hand predicate actually holds for this `a`.
  have h_right :
      (∀ q : ℕ, q ∣ (5 - 1) → q.Prime → ¬ (2 : ZMod 5) ^ ((5 - 1) / q) = 1) := by
    -- Step 2.1: Simplify the arithmetic `5 - 1 = 4`.
    intro q hq hq_prime
    -- Step 2.2: Show that the only prime divisor of `4` is `2`.
    have hq_div_two : q ∣ 2 := by
      have : q ∣ 2 ^ 2 := by simpa [Nat.pow_two] using hq
      exact hq_prime.dvd_of_dvd_pow this
    have hq_two : q = 2 := by
      have h_le : q ≤ 2 := Nat.le_of_dvd (by decide) hq_div_two
      have h_ge : 2 ≤ q := hq_prime.two_le
      exact le_antisymm h_le h_ge
    -- Step 2.3: Check the remaining power when `q = 2`.
    subst hq_two
    have h_div : ((4 : ℕ) / 2) = 2 := by decide
    have h_ne : (2 : ZMod 5) ^ 2 ≠ (1 : ZMod 5) := by decide
    simpa [h_div] using h_ne
  -- Step 3: Show that the left-hand predicate is always false.
  have h_left : ¬ IsPrimitiveRoot (2 : ZMod 5) 5 := by
    intro h
    have h_pow := h.pow_eq_one
    have h_pow_ne : (2 : ZMod 5) ^ 5 ≠ (1 : ZMod 5) := by decide
    exact h_pow_ne (by simpa using h_pow)
  -- Step 4: Conclude that the equivalence cannot hold in this instance.
  intro h_equiv
  have h_primitive : IsPrimitiveRoot (2 : ZMod 5) 5 := (h_equiv.mpr h_right)
  exact h_left h_primitive

/-
Step 0 (corrected statement):  For an odd prime `p` and a unit `a` modulo `p`,
the element `a` has order `p - 1` (hence is a primitive root modulo `p`)
exactly when each prime divisor `q` of `p - 1` yields a non-trivial power
`(a : ZMod p) ^ ((p - 1) / q)`.
-/

theorem Ireland_Rosen_exercise_4_8_corrected {p : ℕ} (hp : Odd p) (hp' : p.Prime) (a : (ZMod p)ˣ) :
  IsPrimitiveRoot (a : ZMod p) (p - 1) ↔
    ∀ q : ℕ, q ∣ (p - 1) → q.Prime →
      ¬ ((a : ZMod p) ^ ((p - 1) / q) = 1) := by
  classical
  -- Step 1: Acknowledge the oddness hypothesis so the linter sees it used.
  have _ := hp
  -- Step 1: Basic numeric facts and type-class instances.
  have h_one_lt_p : 1 < p := hp'.one_lt
  have h_pos : 0 < p - 1 := Nat.sub_pos_of_lt h_one_lt_p
  have h_ne_zero : p - 1 ≠ 0 := ne_of_gt h_pos
  haveI : NeZero p := ⟨hp'.ne_zero⟩
  constructor
  · -- Forward direction: a primitive root forbids those smaller powers.
    intro h_primitive_coe
    -- Step 2: Move to the units viewpoint for group-theoretic tools.
    have h_primitive_units : IsPrimitiveRoot a (p - 1) :=
      (IsPrimitiveRoot.coe_units_iff).mp h_primitive_coe
    -- Step 3: Verify the inequality for each prime divisor.
    intro q hq_div hq_prime h_eq
    -- Step 3.1: Transfer the equality into the units group.
    have h_eq_units :
        a ^ ((p - 1) / q) = (1 : (ZMod p)ˣ) := by
      ext; simpa using h_eq
    -- Step 3.2: Use the primitive root property to deduce divisibility.
    have h_div :=
      (h_primitive_units.pow_eq_one_iff_dvd ((p - 1) / q)).mp h_eq_units
    obtain ⟨t, ht⟩ := h_div
    -- Step 3.3: Reduce to an impossible multiplicative identity.
    have h_mul : q * ((p - 1) / q) = p - 1 := Nat.mul_div_cancel' hq_div
    have h_prod :
        (p - 1) = (p - 1) * (q * t) := by
      calc
        p - 1 = q * ((p - 1) / q) := h_mul.symm
        _ = q * ((p - 1) * t) := by simp [ht]
        _ = (p - 1) * (q * t) := by
          simp [Nat.mul_comm, Nat.mul_assoc]
    have h_cancel :
        1 = q * t := by
      have h_eq' : (p - 1) * 1 = (p - 1) * (q * t) := by simpa using h_prod
      exact (Nat.mul_left_cancel h_pos) h_eq'
    -- Step 3.4: Conclude the contradiction using primality of `q`.
    have h_fact : q * t = 1 := by simpa using h_cancel.symm
    have hq_dvd_one : q ∣ 1 := ⟨t, by simpa [Nat.mul_comm] using h_fact.symm⟩
    have hq_one : q = 1 := Nat.dvd_one.mp hq_dvd_one
    exact hq_prime.ne_one hq_one
  · -- Reverse direction: the power criterion forces primitivity.
    intro h_power
    -- Step 4: Compute the group order and relate it to `orderOf a`.
    have h_card_units :
        Fintype.card (ZMod p)ˣ = p - 1 := by
      simp [Nat.totient_prime hp', ZMod.card_units_eq_totient]
    set m : ℕ := orderOf a
    have h_m_dvd : m ∣ p - 1 := by
      have h_dvd_card : m ∣ Fintype.card (ZMod p)ˣ :=
        orderOf_dvd_card (G := (ZMod p)ˣ) (x := a)
      simpa [m, h_card_units] using h_dvd_card
    have h_m_le : m ≤ p - 1 := Nat.le_of_dvd h_pos h_m_dvd
    -- Step 4.1: Show that `p - 1 ≤ m` using the hypothesis.
    have h_le : p - 1 ≤ m := by
      by_contra h_lt
      obtain ⟨s, hs⟩ := h_m_dvd
      have hm_lt : m < p - 1 := lt_of_not_ge h_lt
      -- Step 4.1.2: `s` cannot be `0` or `1`.
      have h_s_ne_zero : s ≠ 0 := by
        intro hs_zero
        have : p - 1 = 0 := by simpa [hs_zero] using hs
        exact h_ne_zero this
      have h_s_ne_one : s ≠ 1 := by
        intro hs_one
        have h_eq : p - 1 = m := by simpa [hs_one] using hs
        simp [h_eq] at hm_lt
      -- Step 4.1.4: Pick a prime divisor `q` of `s`.
      obtain ⟨q, hq_prime, hq_div_s⟩ :=
        Nat.exists_prime_and_dvd h_s_ne_one
      -- Step 4.1.5: Show that `q` divides `p - 1`.
      have h_s_div : s ∣ p - 1 := ⟨m, by simp [hs, Nat.mul_comm]⟩
      have hq_div_p : q ∣ p - 1 := Nat.dvd_trans hq_div_s h_s_div
      -- Step 4.1.6: Evaluate `(p - 1) / q` explicitly.
      have h_div_expr :
          (p - 1) / q = m * (s / q) := by
        have hkm : s ∣ m * s :=
          ⟨m, by simp [Nat.mul_comm]⟩
        have := Nat.div_mul_div hkm hq_div_s
        have h_div_left : (m * s) / s = m :=
          by
            have := Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero h_s_ne_zero)
            simpa [Nat.mul_comm] using this
        have h_right :
            m * (s / q) = (m * s) / q :=
          by simpa [h_div_left] using this
        have h_right' : m * (s / q) = (p - 1) / q := by simpa [hs] using h_right
        exact h_right'.symm
      -- Step 4.1.7: Deduce that `m` divides `(p - 1) / q`.
      have h_m_div : m ∣ (p - 1) / q := by
        refine ⟨s / q, ?_⟩
        simp [h_div_expr]
      -- Step 4.1.8: Convert the divisibility into a forbidden equality.
      obtain ⟨w, hw⟩ := h_m_div
      have h_pow :
          (a : ZMod p) ^ ((p - 1) / q) = 1 := by
        have h_units_pow : a ^ (m * w) = (1 : (ZMod p)ˣ) := by
          have h_pow_m : a ^ m = (1 : (ZMod p)ˣ) := pow_orderOf_eq_one a
          simp [pow_mul, h_pow_m]
        -- Step 4.1.8.1: Return to the ring using coercions.
        have := congrArg Units.val h_units_pow
        simpa [hw] using this
      -- Step 4.1.9: Contradict the hypothesis with the prime `q`.
      have := h_power q hq_div_p hq_prime
      exact this h_pow
    -- Step 4.2: Combine the bounds to obtain equality.
    have h_order_eq : m = p - 1 := le_antisymm h_m_le h_le
    -- Step 4.3: Assemble the primitive root in the units group.
    have h_primitive_units : IsPrimitiveRoot a (p - 1) := by
      refine ⟨?_, ?_⟩
      · simpa [m, h_order_eq] using pow_orderOf_eq_one a
      · intro l hl
        have h_dvd : orderOf a ∣ l :=
          (orderOf_dvd_iff_pow_eq_one (G := (ZMod p)ˣ) (x := a) (n := l)).2 hl
        simpa [m, h_order_eq] using h_dvd
    -- Step 4.4: Translate back to `ZMod p`.
    exact (IsPrimitiveRoot.coe_units_iff).mpr h_primitive_units
