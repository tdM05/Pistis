import Mathlib

open scoped BigOperators

/-Informal Statement

Prove that there are unique positive integers $a, n$ such that $a^{n+1}-(a+1)^n=2001$.
-/

/-Informal Proof

Suppose $a^{n+1} - (a+1)^n = 2001$.
Notice that $a^{n+1} + [(a+1)^n - 1]$ is a multiple of $a$; thus
$a$ divides $2002 = 2 \times 7 \times 11 \times 13$.

Since $2001$ is divisible by 3, we must have $a \equiv 1 \pmod{3}$,
otherwise one of $a^{n+1}$ and $(a+1)^n$ is a multiple of 3 and the
other is not, so their difference cannot be divisible by 3. Now
$a^{n+1} \equiv 1 \pmod{3}$, so we must have $(a+1)^n \equiv 1
\pmod{3}$, which forces $n$ to be even, and in particular at least 2.

If $a$ is even, then $a^{n+1} - (a+1)^n \equiv -(a+1)^n \pmod{4}$.
Since $n$ is even, $-(a+1)^n \equiv -1 \pmod{4}$. Since $2001 \equiv 1
\pmod{4}$, this is impossible. Thus $a$ is odd, and so must divide
$1001 = 7 \times 11 \times 13$. Moreover, $a^{n+1} - (a+1)^n \equiv a
\pmod{4}$, so $a \equiv 1 \pmod{4}$.

Of the divisors of $7 \times 11 \times 13$, those congruent to 1 mod 3
are precisely those not divisible by 11 (since 7 and 13 are both
congruent to 1 mod 3). Thus $a$ divides $7 \times 13$. Now
$a \equiv 1 \pmod{4}$ is only possible if $a$ divides $13$.

We cannot have $a=1$, since $1 - 2^n \neq 2001$ for any $n$. Thus
the only possibility is $a = 13$. One easily checks that $a=13, n=2$ is a
solution; all that remains is to check that no other $n$ works. In fact,
if $n > 2$, then $13^{n+1} \equiv 2001 \equiv 1 \pmod{8}$.
But $13^{n+1} \equiv 13 \pmod{8}$ since $n$ is even, contradiction.
Thus $a=13, n=2$ is the unique solution.

Note: once one has that $n$ is even, one can use that $2002
=a^{n+1} + 1 - (a+1)^n$ is divisible by $a+1$ to rule out cases.
-/

/-!
## Formal Proof

The unique solution to a^(n+1) - (a+1)^n = 2001 with a, n > 0 is (a, n) = (13, 2).
-/

-- Verify the solution
lemma pow_diff_eq_2001 : (13 : ℕ)^3 - 14^2 = 2001 := by native_decide

-- Helper: underflow propagates forward
lemma underflow_propagate {a : ℕ} (ha : a ≥ 2) {k : ℕ} (hbase : a^(k+1) < (a+1)^k)
    {n : ℕ} (hn : n ≥ k) : a^(n+1) < (a+1)^n := by
  induction n with
  | zero =>
    have : k = 0 := Nat.le_zero.mp hn
    subst this; exact hbase
  | succ m ih =>
    rcases Nat.lt_or_ge m k with hm | hm
    · have : m + 1 = k := by omega
      simp only [this] at *; exact hbase
    · have ih' := ih hm
      have hpos : (a+1)^m > 0 := Nat.pow_pos (by omega)
      calc a^(m+1+1) = a * a^(m+1) := by ring
        _ < a * (a+1)^m := Nat.mul_lt_mul_of_pos_left ih' (by omega)
        _ < (a+1) * (a+1)^m := Nat.mul_lt_mul_of_pos_right (by omega) hpos
        _ = (a+1)^(m+1) := by ring

-- For a = 1: 1 - 2^n = 0 for n ≥ 1 (underflow)
lemma a_eq_1_no_sol (n : ℕ) (hn : n > 0) : (1 : ℕ)^(n+1) - 2^n ≠ 2001 := by
  simp only [one_pow]
  have h : 2^n ≥ 2 := Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp hn)
  omega

-- For a = 2: crossover at n = 2
lemma a_eq_2_no_sol (n : ℕ) (hn : n > 0) : (2 : ℕ)^(n+1) - 3^n ≠ 2001 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n; native_decide
  · have hbase : (2 : ℕ)^3 < 3^2 := by native_decide
    have huf := underflow_propagate (by norm_num : (2 : ℕ) ≥ 2) hbase h
    simp [Nat.sub_eq_zero_of_le (le_of_lt huf)]

-- For a = 7: crossover at n = 15
lemma a_eq_7_no_sol (n : ℕ) (hn : n > 0) : (7 : ℕ)^(n+1) - 8^n ≠ 2001 := by
  rcases Nat.lt_or_ge n 15 with h | h
  · interval_cases n <;> native_decide
  · have hbase : (7 : ℕ)^16 < 8^15 := by native_decide
    have huf := underflow_propagate (by norm_num) hbase h
    simp [Nat.sub_eq_zero_of_le (le_of_lt huf)]

-- For a = 11: crossover at n = 28
lemma a_eq_11_no_sol (n : ℕ) (hn : n > 0) : (11 : ℕ)^(n+1) - 12^n ≠ 2001 := by
  rcases Nat.lt_or_ge n 28 with h | h
  · interval_cases n <;> native_decide
  · have hbase : (11 : ℕ)^29 < 12^28 := by native_decide
    have huf := underflow_propagate (by norm_num) hbase h
    simp [Nat.sub_eq_zero_of_le (le_of_lt huf)]

-- For a = 13: only n = 2 works; crossover at n = 35
lemma a_eq_13_n_ne_2 (n : ℕ) (hn : n > 0) (hn2 : n ≠ 2) : (13 : ℕ)^(n+1) - 14^n ≠ 2001 := by
  rcases Nat.lt_or_ge n 35 with h | h
  · rcases Nat.lt_or_gt_of_ne hn2 with hn' | hn'
    · interval_cases n; native_decide
    · interval_cases n <;> native_decide
  · have hbase : (13 : ℕ)^36 < 14^35 := by native_decide
    have huf := underflow_propagate (by norm_num) hbase h
    simp [Nat.sub_eq_zero_of_le (le_of_lt huf)]

-- For a = 14: crossover at n = 39
lemma a_eq_14_no_sol (n : ℕ) (hn : n > 0) : (14 : ℕ)^(n+1) - 15^n ≠ 2001 := by
  rcases Nat.lt_or_ge n 39 with h | h
  · interval_cases n <;> native_decide
  · have hbase : (14 : ℕ)^40 < 15^39 := by native_decide
    have huf := underflow_propagate (by norm_num) hbase h
    simp [Nat.sub_eq_zero_of_le (le_of_lt huf)]

-- For a = 22: crossover at n = 70
lemma a_eq_22_no_sol (n : ℕ) (hn : n > 0) : (22 : ℕ)^(n+1) - 23^n ≠ 2001 := by
  rcases Nat.lt_or_ge n 70 with h | h
  · interval_cases n <;> native_decide
  · have hbase : (22 : ℕ)^71 < 23^70 := by native_decide
    have huf := underflow_propagate (by norm_num) hbase h
    simp [Nat.sub_eq_zero_of_le (le_of_lt huf)]

-- For a = 26: crossover at n = 87
lemma a_eq_26_no_sol (n : ℕ) (hn : n > 0) : (26 : ℕ)^(n+1) - 27^n ≠ 2001 := by
  rcases Nat.lt_or_ge n 87 with h | h
  · interval_cases n <;> native_decide
  · have hbase : (26 : ℕ)^88 < 27^87 := by native_decide
    have huf := underflow_propagate (by norm_num) hbase h
    simp [Nat.sub_eq_zero_of_le (le_of_lt huf)]

/-!
## Approach for large divisors (a ≥ 77)

For large a, we use a modular arithmetic argument.
Key insight: a ≡ -1 (mod a+1), so:
- a^(n+1) ≡ (-1)^(n+1) (mod a+1)
- (a+1)^n ≡ 0 (mod a+1) for n ≥ 1
- So a^(n+1) - (a+1)^n ≡ (-1)^(n+1) (mod a+1)

This means the difference mod (a+1) is either 1 (if n+1 is even) or a (if n+1 is odd).
If 2001 mod (a+1) is neither 1 nor a, then diff ≠ 2001.
-/

-- Helper: when y % m = 0 and x ≥ y, then (x - y) % m = x % m
lemma sub_mod_of_mod_eq_zero (x y m : ℕ) (hy : y % m = 0) (hge : x ≥ y) : (x - y) % m = x % m := by
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hy
  subst hk
  have hmk : m * k ≤ x := hge
  conv_rhs => rw [← Nat.sub_add_cancel hmk]
  simp only [Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod]

-- Helper lemma: pow of (a+1) divisible by (a+1) for n ≥ 1
lemma pow_succ_mod_self (a n : ℕ) : (a+1)^(n+1) % (a+1) = 0 := by
  have h : (a+1)^(n+1) = (a+1) * (a+1)^n := by ring
  rw [h, Nat.mul_mod_right]

-- Helper lemma: a * a = (a+1) * (a-1) + 1 for a ≥ 1
lemma sq_eq_succ_mul_pred_add_one (a : ℕ) (ha : a ≥ 1) : a * a = (a+1) * (a-1) + 1 := by
  cases a with
  | zero => omega
  | succ n =>
    -- a = n + 1, so a-1 = n, a+1 = n+2
    -- (n+1)*(n+1) = (n+2)*n + 1 = n^2 + 2n + 1
    simp only [Nat.add_one_sub_one]
    -- Goal: (n + 1) * (n + 1) = (n + 1 + 1) * n + 1
    -- = (n + 2) * n + 1 = n^2 + 2n + 1
    -- LHS = n^2 + 2n + 1
    calc (n + 1) * (n + 1) = n * n + 2 * n + 1 := by ring
      _ = (n + 2) * n + 1 := by ring
      _ = (n + 1 + 1) * n + 1 := by ring

-- Helper lemma: a^k mod (a+1) is 1 if k is even, a if k is odd (for a ≥ 1)
lemma pow_mod_succ (a k : ℕ) (ha : a ≥ 1) : a^k % (a+1) = if k % 2 = 0 then 1 else a := by
  induction k with
  | zero =>
    simp only [pow_zero, Nat.zero_mod, ↓reduceIte]
    exact Nat.mod_eq_of_lt (by omega)
  | succ m ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    have ha_mod : a % (a+1) = a := Nat.mod_eq_of_lt (by omega)
    have h_aa : a * a % (a+1) = 1 := by
      have h2 : a * a = (a+1) * (a-1) + 1 := sq_eq_succ_mul_pred_add_one a ha
      rw [h2, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]
      exact Nat.mod_eq_of_lt (by omega)
    rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- m even, m+1 odd
      have hm_even : m % 2 = 0 := by omega
      have hm1_odd : (m+1) % 2 = 1 := by omega
      simp only [hm_even, ↓reduceIte, Nat.one_mul, hm1_odd]
      rw [Nat.mod_mod]
      exact ha_mod
    · -- m odd, m+1 even
      have hm_odd : m % 2 = 1 := by omega
      have hm1_even : (m+1) % 2 = 0 := by omega
      simp only [hm_odd, ↓reduceIte, hm1_even]
      -- goal is (if 1 = 0 then 1 else a) * a % (a+1) = 1
      -- (if 1 = 0 then 1 else a) = a
      have h1ne0 : (1 : ℕ) ≠ 0 := by norm_num
      simp only [h1ne0, ↓reduceIte]
      rw [ha_mod, h_aa]

-- Helper for difference mod (a+1)
lemma diff_mod_succ {a n : ℕ} (ha : a ≥ 1) (hn : n > 0) (huf : (a+1)^n < a^(n+1)) :
    (a^(n+1) - (a+1)^n) % (a+1) = if (n+1) % 2 = 0 then 1 else a := by
  have hdiv_zero : (a+1)^n % (a+1) = 0 := by
    cases n with
    | zero => omega
    | succ m => exact pow_succ_mod_self a m
  have ha_pow_mod : a^(n+1) % (a+1) = if (n+1) % 2 = 0 then 1 else a := pow_mod_succ a (n+1) ha
  have hge : a^(n+1) ≥ (a+1)^n := le_of_lt huf
  rw [sub_mod_of_mod_eq_zero _ _ _ hdiv_zero hge, ha_pow_mod]

-- Generic large divisor lemma
lemma large_a_no_sol (a : ℕ) (ha : a ≥ 77) (hmod : 2001 % (a+1) ≠ 1 ∧ 2001 % (a+1) ≠ a)
    (n : ℕ) (hn : n > 0) : a^(n+1) - (a+1)^n ≠ 2001 := by
  intro heq
  by_cases huf : a^(n+1) ≤ (a+1)^n
  · simp only [Nat.sub_eq_zero_of_le huf] at heq; omega
  · push_neg at huf
    have ha_pos : a ≥ 1 := by omega
    have hdiff_mod := diff_mod_succ ha_pos hn huf
    rw [heq] at hdiff_mod
    split_ifs at hdiff_mod with heven
    · exact hmod.1 hdiff_mod
    · exact hmod.2 hdiff_mod

-- For a = 77: 2001 % 78 = 51, which is neither 1 nor 77
lemma a_eq_77_no_sol (n : ℕ) (hn : n > 0) : (77 : ℕ)^(n+1) - 78^n ≠ 2001 :=
  large_a_no_sol 77 (by norm_num) ⟨by native_decide, by native_decide⟩ n hn

-- For a = 91: 2001 % 92 = 69, which is neither 1 nor 91
lemma a_eq_91_no_sol (n : ℕ) (hn : n > 0) : (91 : ℕ)^(n+1) - 92^n ≠ 2001 :=
  large_a_no_sol 91 (by norm_num) ⟨by native_decide, by native_decide⟩ n hn

-- For a = 143: 2001 % 144 = 129, which is neither 1 nor 143
lemma a_eq_143_no_sol (n : ℕ) (hn : n > 0) : (143 : ℕ)^(n+1) - 144^n ≠ 2001 :=
  large_a_no_sol 143 (by norm_num) ⟨by native_decide, by native_decide⟩ n hn

-- For a = 154: 2001 % 155 = 141, which is neither 1 nor 154
lemma a_eq_154_no_sol (n : ℕ) (hn : n > 0) : (154 : ℕ)^(n+1) - 155^n ≠ 2001 :=
  large_a_no_sol 154 (by norm_num) ⟨by native_decide, by native_decide⟩ n hn

-- For a = 182: 2001 % 183 = 177, which is neither 1 nor 182
lemma a_eq_182_no_sol (n : ℕ) (hn : n > 0) : (182 : ℕ)^(n+1) - 183^n ≠ 2001 :=
  large_a_no_sol 182 (by norm_num) ⟨by native_decide, by native_decide⟩ n hn

-- For a = 286: 2001 % 287 = 280, which is neither 1 nor 286
lemma a_eq_286_no_sol (n : ℕ) (hn : n > 0) : (286 : ℕ)^(n+1) - 287^n ≠ 2001 :=
  large_a_no_sol 286 (by norm_num) ⟨by native_decide, by native_decide⟩ n hn

-- For a = 1001: 2001 % 1002 = 999, which is neither 1 nor 1001
lemma a_eq_1001_no_sol (n : ℕ) (hn : n > 0) : (1001 : ℕ)^(n+1) - 1002^n ≠ 2001 :=
  large_a_no_sol 1001 (by norm_num) ⟨by native_decide, by native_decide⟩ n hn

-- For a = 2002: 2001 % 2003 = 2001, which is neither 1 nor 2002
lemma a_eq_2002_no_sol (n : ℕ) (hn : n > 0) : (2002 : ℕ)^(n+1) - 2003^n ≠ 2001 :=
  large_a_no_sol 2002 (by norm_num) ⟨by native_decide, by native_decide⟩ n hn

-- Helper: (a+1)^n ≡ 1 (mod a)
lemma pow_succ_mod_base (a n : ℕ) : (a+1)^n % a = 1 % a := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Nat.mul_mod]
    have h1 : (a+1) % a = 1 % a := by rw [Nat.add_comm]; exact Nat.add_mod_right 1 a
    rw [h1, ih, ← Nat.mul_mod, Nat.one_mul]

-- Key divisibility lemma
lemma div_2002_of_pow_diff_eq_2001 {a n : ℕ} (ha : a > 0) (hn : n > 0)
    (h : a^(n+1) - (a+1)^n = 2001) : a ∣ 2002 := by
  by_cases huf : a^(n+1) ≤ (a+1)^n
  · simp [Nat.sub_eq_zero_of_le huf] at h
  · push_neg at huf
    -- (a+1)^n ≡ 1 (mod a) since (a+1) ≡ 1 (mod a)
    have hbinom : (a+1)^n % a = 1 % a := pow_succ_mod_base a n
    -- a^(n+1) ≡ 0 (mod a)
    have h1 : a^(n+1) % a = 0 := by
      cases n with
      | zero => simp
      | succ m =>
        have : a^(m+2) = a * a^(m+1) := by ring
        rw [this, Nat.mul_mod_right]
    -- diff ≡ 0 - 1 ≡ a-1 (mod a)
    have h3 : 2001 % a = (a^(n+1) - (a+1)^n) % a := by rw [h]
    have hge : a^(n+1) ≥ (a+1)^n := le_of_lt huf
    have h4 : (a^(n+1) - (a+1)^n) % a = (a - 1 % a) % a := by
      rcases Nat.lt_or_ge a 2 with ha' | ha'
      · interval_cases a; simp_all
      · have h1a : 1 % a = 1 := Nat.mod_eq_of_lt (by omega)
        rw [h1a]
        have hbinom' : (a+1)^n % a = 1 := by rw [hbinom, h1a]
        -- x - y where x % a = 0, y % a = 1, x > y
        have hdiff_mod : (a^(n+1) - (a+1)^n) % a = (a - 1) % a := by
          have hx0 : a^(n+1) % a = 0 := h1
          have hy1 : (a+1)^n % a = 1 := hbinom'
          obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hx0
          have hy_form : ∃ r, (a+1)^n = a * r + 1 := by
            use ((a+1)^n) / a
            have := Nat.div_add_mod ((a+1)^n) a
            rw [hy1] at this; omega
          obtain ⟨r, hr⟩ := hy_form
          have hqr : a * q ≥ a * r + 1 := by rw [← hq, ← hr]; exact hge
          have hq_gt_r : q > r := by
            by_contra hle; push_neg at hle
            have : a * q ≤ a * r := Nat.mul_le_mul_left a hle; omega
          rw [hq, hr]
          -- We want to show (a*q - (a*r + 1)) % a = (a-1) % a
          -- Since a*q and a*r are both divisible by a, a*q - a*r is divisible by a
          -- So (a*q - (a*r + 1)) % a = (a*q - a*r - 1) % a = (0 - 1) % a = (a - 1) % a
          -- Direct approach using sub_mod_of_mod_eq_zero
          have hdiff : (a * q - (a * r + 1)) % a = (a - 1) % a := by
            -- a * q - (a * r + 1) = a * q - a * r - 1 = a * (q - r) - 1
            have hqr_pos : q - r ≥ 1 := by omega
            have hrewrite : a * q - (a * r + 1) = a * (q - r) - 1 := by
              have h1 : a * q - a * r = a * (q - r) := (Nat.mul_sub_left_distrib a q r).symm
              have h2 : a * q ≥ a * r := Nat.mul_le_mul_left a (le_of_lt hq_gt_r)
              omega
            rw [hrewrite]
            -- Now show (a * (q - r) - 1) % a = (a - 1) % a
            -- Since a * (q - r) % a = 0 and a * (q - r) ≥ a ≥ 1
            have hmul_mod : a * (q - r) % a = 0 := Nat.mul_mod_right a (q - r)
            have hmul_ge : a * (q - r) ≥ a := Nat.le_mul_of_pos_right a hqr_pos
            have hmul_ge1 : a * (q - r) ≥ 1 := le_trans (by omega : 1 ≤ a) hmul_ge
            -- (a * (q - r) - 1) % a = (a * (q - r) % a + (a - 1)) % a = (0 + (a - 1)) % a = (a - 1) % a
            -- Use: for x ≥ 1 with x % a = 0, (x - 1) % a = (a - 1) % a
            have hsub_one_mod : ∀ x : ℕ, x ≥ 1 → x % a = 0 → (x - 1) % a = (a - 1) % a := by
              intro x hx1 hxmod
              obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hxmod
              rcases Nat.eq_zero_or_pos k with rfl | hkpos
              · simp at hk; omega
              · -- x = a * k with k ≥ 1, so x - 1 = a * k - 1 = a * (k - 1) + (a - 1)
                have hk_form : a * k - 1 = a * (k - 1) + (a - 1) := by
                  have : a * k = a * (k - 1) + a := by
                    rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right a hkpos)]
                  omega
                rw [hk, hk_form, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]
            exact hsub_one_mod _ hmul_ge1 hmul_mod
          rw [hdiff]
        rw [hdiff_mod, Nat.mod_eq_of_lt (by omega : a - 1 < a)]
    rw [h4] at h3
    have h5 : 2002 % a = 0 := by
      rcases Nat.lt_or_ge a 2 with ha1 | ha1
      · interval_cases a; omega
      · have h1a : 1 % a = 1 := Nat.mod_eq_of_lt (by omega : 1 < a)
        have ha_sub : (a - 1) % a = a - 1 := Nat.mod_eq_of_lt (by omega : a - 1 < a)
        have h6 : 2001 % a = (a - 1) % a := by rw [h3, h1a, ha_sub]
        have h7 : 2001 % a = a - 1 := by rw [h6, ha_sub]
        have : 2002 % a = (2001 + 1) % a := by ring_nf
        rw [this, Nat.add_mod, h7]
        have : (a - 1 + 1) % a = 0 := by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ a), Nat.mod_self]
        rw [Nat.mod_eq_of_lt (by omega : 1 < a), this]
    exact Nat.dvd_of_mod_eq_zero h5

/-- Main theorem: (13, 2) is the unique solution. -/
theorem Putnam_exercise_2001_a5 :
    ∃! p : ℕ × ℕ, p.1 > 0 ∧ p.2 > 0 ∧ p.1^(p.2 + 1) - (p.1 + 1)^(p.2) = 2001 := by
  use (13, 2)
  constructor
  · exact ⟨by norm_num, by norm_num, pow_diff_eq_2001⟩
  · intro ⟨a, n⟩ ⟨ha_pos, hn_pos, h_eq⟩
    simp only [Prod.mk.injEq]
    have hdiv : a ∣ 2002 := div_2002_of_pow_diff_eq_2001 ha_pos hn_pos h_eq
    have hdivs : a ∈ ({1, 2, 7, 11, 13, 14, 22, 26, 77, 91, 143, 154, 182, 286, 1001, 2002} : Finset ℕ) := by
      have h2002 : (2002 : ℕ).divisors = {1, 2, 7, 11, 13, 14, 22, 26, 77, 91, 143, 154, 182, 286, 1001, 2002} := by native_decide
      rw [← h2002]
      exact Nat.mem_divisors.mpr ⟨hdiv, by norm_num⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdivs
    rcases hdivs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd h_eq (a_eq_1_no_sol n hn_pos)
    · exact absurd h_eq (a_eq_2_no_sol n hn_pos)
    · exact absurd h_eq (a_eq_7_no_sol n hn_pos)
    · exact absurd h_eq (a_eq_11_no_sol n hn_pos)
    · rcases eq_or_ne n 2 with rfl | hn2
      · exact ⟨rfl, rfl⟩
      · exact absurd h_eq (a_eq_13_n_ne_2 n hn_pos hn2)
    · exact absurd h_eq (a_eq_14_no_sol n hn_pos)
    · exact absurd h_eq (a_eq_22_no_sol n hn_pos)
    · exact absurd h_eq (a_eq_26_no_sol n hn_pos)
    · exact absurd h_eq (a_eq_77_no_sol n hn_pos)
    · exact absurd h_eq (a_eq_91_no_sol n hn_pos)
    · exact absurd h_eq (a_eq_143_no_sol n hn_pos)
    · exact absurd h_eq (a_eq_154_no_sol n hn_pos)
    · exact absurd h_eq (a_eq_182_no_sol n hn_pos)
    · exact absurd h_eq (a_eq_286_no_sol n hn_pos)
    · exact absurd h_eq (a_eq_1001_no_sol n hn_pos)
    · exact absurd h_eq (a_eq_2002_no_sol n hn_pos)
