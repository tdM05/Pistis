import Mathlib

open scoped BigOperators



/-Informal Statement

Prove that, for any integers $a, b, c$, there exists a positive integer $n$ such that $\sqrt{n^3+a n^2+b n+c}$ is not an integer.
-/

/-Informal Proof

We prove more generally that for any polynomial $P(z)$ with integer
coefficients which is not a perfect square, there exists a positive
integer $n$ such that $P(n)$ is not a perfect square. Of course it
suffices to assume $P(z)$ has no repeated factors, which is to say $P(z)$
and its derivative $P'(z)$ are relatively prime.

In particular, if we carry out the Euclidean algorithm on $P(z)$ and $P'(z)$
without dividing, we get an integer $D$ (the discriminant of $P$) such that
the greatest common divisor of $P(n)$ and $P'(n)$ divides $D$ for any $n$.
Now there exist infinitely many primes $p$ such that $p$ divides $P(n)$ for
some $n$: if there were only finitely many, say, $p_1, \dots, p_k$, then
for any $n$ divisible by $m = P(0) p_1 p_2 \cdots p_k$, we have $P(n)
\equiv P(0) \pmod{m}$, that is, $P(n)/P(0)$ is not divisible by $p_1,
\dots, p_k$, so must be $\pm 1$, but then $P$ takes some value infinitely
many times, contradiction. In particular, we can choose some such $p$ not
dividing $D$, and choose $n$ such that $p$ divides $P(n)$. Then $P(n+kp)
\equiv P(n) + kp P'(n) (\mathrm{mod}\,p)$
(write out the Taylor series of the left side);
in particular, since $p$ does not divide $P'(n)$, we can find some $k$
such that $P(n+kp)$ is divisible by $p$ but not by $p^2$, and so
is not a perfect square.
-/

/-!
## Proof Strategy

We use a mod 4 argument to show that for any integers a, b, c, there exists a positive
integer n such that P(n) = n³ + an² + bn + c is positive and ≡ 2 or 3 (mod 4).
Since perfect squares are always ≡ 0 or 1 (mod 4), such P(n) cannot be a perfect square,
and therefore √P(n) is not an integer.

### Step 1: Squares are 0 or 1 mod 4
Any integer m has m² ≡ 0 or 1 (mod 4). This is because:
- If m ≡ 0 (mod 4), then m² ≡ 0 (mod 4)
- If m ≡ 1 (mod 4), then m² ≡ 1 (mod 4)
- If m ≡ 2 (mod 4), then m² ≡ 0 (mod 4)
- If m ≡ 3 (mod 4), then m² ≡ 1 (mod 4)

### Step 2: Mod 4 coverage
For any a, b, c, at least one of P(1), P(2), P(3), P(4) is ≡ 2 or 3 (mod 4).
This can be verified by exhaustive computation over all 64 cases of (a mod 4, b mod 4, c mod 4).

### Step 3: Periodicity
P(n + 4k) ≡ P(n) (mod 4) for all integers n, k.

### Step 4: Eventually positive
For large enough n, P(n) > 0 (since the leading term n³ dominates).

### Step 5: Combining the arguments
Find r ∈ {1, 2, 3, 4} with P(r) ≡ 2 or 3 (mod 4).
Choose k large enough so that n = r + 4k > 0 and P(n) > 0.
Then P(n) ≡ P(r) ≡ 2 or 3 (mod 4), so P(n) is not a perfect square.
Therefore √P(n) is not an integer.
-/

-- =============================================================================
-- Step 1: Key lemma about squares mod 4
-- =============================================================================

/-- Step 1.1: Any integer squared is congruent to 0 or 1 mod 4.
    This follows from checking the four residue classes mod 4:
    - 0² ≡ 0 (mod 4)
    - 1² ≡ 1 (mod 4)
    - 2² ≡ 0 (mod 4)
    - 3² ≡ 1 (mod 4) -/
lemma sq_mod_four (m : ℤ) : m^2 % 4 = 0 ∨ m^2 % 4 = 1 := by
  -- Step 1.1.1: m mod 4 is one of 0, 1, 2, 3
  have hmod : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  -- Step 1.1.2: m² mod 4 = (m mod 4)² mod 4
  have key : m^2 % 4 = (m % 4)^2 % 4 := by
    have h1 : m = m / 4 * 4 + m % 4 := (Int.ediv_mul_add_emod m 4).symm
    conv_lhs => rw [h1]
    ring_nf
    omega
  -- Step 1.1.3: Check each case
  rcases hmod with h0 | h1 | h2 | h3
  · left; rw [key, h0]; norm_num   -- 0² ≡ 0 mod 4
  · right; rw [key, h1]; norm_num  -- 1² ≡ 1 mod 4
  · left; rw [key, h2]; norm_num   -- 2² ≡ 0 mod 4
  · right; rw [key, h3]; norm_num  -- 3² ≡ 1 mod 4

/-- Step 1.2: If x ≡ 2 or 3 (mod 4), then x is not a perfect square.
    This is the contrapositive of Step 1.1. -/
lemma not_sq_of_mod4_eq_two_or_three (x : ℤ) (hx : x % 4 = 2 ∨ x % 4 = 3) :
    ¬ ∃ m : ℤ, m^2 = x := by
  intro ⟨m, hm⟩
  have h := sq_mod_four m
  subst hm
  omega

-- =============================================================================
-- Step 2: Define the polynomial P and establish basic properties
-- =============================================================================

/-- Step 2.1: Define P(n) = n³ + an² + bn + c -/
def P_poly (a b c n : ℤ) : ℤ := n^3 + a*n^2 + b*n + c

/-- Step 2.2: P(n + 4k) ≡ P(n) (mod 4) for all integers n, k.
    This is because adding 4k to n doesn't change the value mod 4. -/
lemma P_mod4_add_four_mul (a b c n k : ℤ) :
    P_poly a b c (n + 4*k) % 4 = P_poly a b c n % 4 := by
  unfold P_poly
  ring_nf
  omega

-- =============================================================================
-- Step 3: Mod 4 coverage - at least one of P(1), P(2), P(3), P(4) is 2 or 3 mod 4
-- =============================================================================

/-- Step 3.1: For any integers a, b, c, at least one of P(1), P(2), P(3), P(4)
    is congruent to 2 or 3 modulo 4.

    This is verified by exhaustive computation. The key simplifications are:
    - P(1) = 1 + a + b + c
    - P(2) = 8 + 4a + 2b + c ≡ 2b + c (mod 4)
    - P(3) = 27 + 9a + 3b + c ≡ 3 + a + 3b + c (mod 4)
    - P(4) = 64 + 16a + 4b + c ≡ c (mod 4)

    For any choice of (a mod 4, b mod 4, c mod 4), at least one of these
    four expressions is 2 or 3 mod 4. -/
lemma mod4_coverage (a b c : ℤ) :
    P_poly a b c 1 % 4 = 2 ∨ P_poly a b c 1 % 4 = 3 ∨
    P_poly a b c 2 % 4 = 2 ∨ P_poly a b c 2 % 4 = 3 ∨
    P_poly a b c 3 % 4 = 2 ∨ P_poly a b c 3 % 4 = 3 ∨
    P_poly a b c 4 % 4 = 2 ∨ P_poly a b c 4 % 4 = 3 := by
  unfold P_poly
  ring_nf
  omega

-- =============================================================================
-- Step 4: The polynomial is eventually positive
-- =============================================================================

/-- Step 4.1: For large enough n, P(n) > 0.
    This is because the cubic term n³ eventually dominates the lower-order terms.
    Specifically, for n ≥ 2(|a| + |b| + |c|) + 1, we have P(n) > 0. -/
lemma cubic_eventually_positive (a b c : ℤ) :
    ∃ N : ℤ, N > 0 ∧ ∀ n : ℤ, n ≥ N → P_poly a b c n > 0 := by
  -- Step 4.1.1: Choose N = 2(|a| + |b| + |c|) + 1
  use 2 * (|a| + |b| + |c|) + 1
  constructor
  · -- Step 4.1.2: N > 0
    have h : (|a| + |b| + |c|) ≥ 0 := by positivity
    omega
  · -- Step 4.1.3: For all n ≥ N, P(n) > 0
    intro n hn
    unfold P_poly
    -- Step 4.1.4: First show n > 0
    have h_pos : n > 0 := by
      have h1 : (2 * (|a| + |b| + |c|) + 1 : ℤ) > 0 := by
        have h : (|a| + |b| + |c|) ≥ 0 := by positivity
        omega
      omega
    -- Step 4.1.5: Lower bound: n³ + an² + bn + c ≥ n³ - |a|n² - |b|n - |c|
    have h_bound : n^3 + a*n^2 + b*n + c ≥ n^3 - (|a|)*(n^2) - (|b|)*n - |c| := by
      have ha : a * n^2 ≥ -(|a|) * n^2 := by have := neg_abs_le a; nlinarith [sq_nonneg n]
      have hb : b * n ≥ -(|b|) * n := by have := neg_abs_le b; nlinarith
      have hc : c ≥ -|c| := neg_abs_le c
      linarith
    -- Step 4.1.6: Show n³ - |a|n² - |b|n - |c| > 0 for n ≥ N
    have key : n^3 - (|a|)*(n^2) - (|b|)*n - |c| > 0 := by
      set A := |a|; set B := |b|; set C := |c|
      have hA_nn : A ≥ 0 := abs_nonneg a
      have hB_nn : B ≥ 0 := abs_nonneg b
      have hC_nn : C ≥ 0 := abs_nonneg c
      have hn2 : n ≥ 2 * (A + B + C) + 1 := hn
      have hn_ge_1 : n ≥ 1 := by omega
      -- n² ≥ (2(A+B+C)+1) · n
      have hn_sq : n^2 ≥ (2 * (A + B + C) + 1) * n := by nlinarith
      -- n³ ≥ (2(A+B+C)+1) · n²
      have hn_cub : n^3 ≥ (2 * (A + B + C) + 1) * n^2 := by nlinarith
      nlinarith
    linarith

-- =============================================================================
-- Step 5: Combine to find a positive n with P(n) not a perfect square
-- =============================================================================

/-- Step 5.1: There exists n > 0 with P(n) > 0 and P(n) ≡ 2 or 3 (mod 4).
    We use the mod 4 coverage (Step 3) to find r ∈ {1,2,3,4} with P(r) ≡ 2 or 3 (mod 4),
    then use periodicity (Step 2) to extend to n = r + 4k for large enough k
    where P(n) > 0 (Step 4). -/
lemma exists_positive_non_sq (a b c : ℤ) :
    ∃ n : ℤ, n > 0 ∧ P_poly a b c n > 0 ∧ (P_poly a b c n % 4 = 2 ∨ P_poly a b c n % 4 = 3) := by
  -- Step 5.1.1: Get the positivity threshold N
  obtain ⟨N, hN_pos, hN⟩ := cubic_eventually_positive a b c
  -- Step 5.1.2: Get the mod 4 coverage
  have hcover := mod4_coverage a b c
  -- Step 5.1.3: Choose k = max(0, N) so that r + 4k ≥ N for r ∈ {1,2,3,4}
  set k := max 0 N
  have hk_nn : k ≥ 0 := le_max_left 0 _
  have hk_large : k ≥ N := le_max_right 0 _
  -- Step 5.1.4: Verify that r + 4k ≥ N and r + 4k > 0 for r ∈ {1,2,3,4}
  have h1_ge : 1 + 4 * k ≥ N := by omega
  have h2_ge : 2 + 4 * k ≥ N := by omega
  have h3_ge : 3 + 4 * k ≥ N := by omega
  have h4_ge : 4 + 4 * k ≥ N := by omega
  have h1_pos : 1 + 4 * k > 0 := by omega
  have h2_pos : 2 + 4 * k > 0 := by omega
  have h3_pos : 3 + 4 * k > 0 := by omega
  have h4_pos : 4 + 4 * k > 0 := by omega
  -- Step 5.1.5: Use the coverage to find the right residue class
  rcases hcover with h1 | h1 | h2 | h2 | h3 | h3 | h4 | h4
  all_goals first
  | exact ⟨1 + 4 * k, h1_pos, hN _ h1_ge, Or.inl (by rw [P_mod4_add_four_mul]; assumption)⟩
  | exact ⟨1 + 4 * k, h1_pos, hN _ h1_ge, Or.inr (by rw [P_mod4_add_four_mul]; assumption)⟩
  | exact ⟨2 + 4 * k, h2_pos, hN _ h2_ge, Or.inl (by rw [P_mod4_add_four_mul]; assumption)⟩
  | exact ⟨2 + 4 * k, h2_pos, hN _ h2_ge, Or.inr (by rw [P_mod4_add_four_mul]; assumption)⟩
  | exact ⟨3 + 4 * k, h3_pos, hN _ h3_ge, Or.inl (by rw [P_mod4_add_four_mul]; assumption)⟩
  | exact ⟨3 + 4 * k, h3_pos, hN _ h3_ge, Or.inr (by rw [P_mod4_add_four_mul]; assumption)⟩
  | exact ⟨4 + 4 * k, h4_pos, hN _ h4_ge, Or.inl (by rw [P_mod4_add_four_mul]; assumption)⟩
  | exact ⟨4 + 4 * k, h4_pos, hN _ h4_ge, Or.inr (by rw [P_mod4_add_four_mul]; assumption)⟩

-- =============================================================================
-- Step 6: Main theorem
-- =============================================================================

theorem Putnam_exercise_1998_b6 (a b c : ℤ) :
    ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  -- Step 6.1: Get n with P(n) > 0 and P(n) ≡ 2 or 3 (mod 4)
  obtain ⟨n, hn_pos, hPn_pos, hPn_mod4⟩ := exists_positive_non_sq a b c
  use n
  constructor
  · exact hn_pos
  · -- Step 6.2: P(n) is not a perfect square (by mod 4 argument)
    have hPn_not_sq : ¬ ∃ m : ℤ, m^2 = P_poly a b c n := not_sq_of_mod4_eq_two_or_three _ hPn_mod4
    -- Step 6.3: Connect P_poly to the expression in the goal
    have hP_eq : P_poly a b c n = n^3 + a*n^2 + b*n + c := by unfold P_poly; ring
    -- Step 6.4: Show √P(n) is not an integer
    intro ⟨m, hm⟩
    apply hPn_not_sq
    use m
    -- Step 6.5: The goal expression (n³+an²+bn+c as reals) equals P(n)
    have hP_real : (n^3 + a*n^2 + b*n + c : ℝ) = (P_poly a b c n : ℝ) := by
      unfold P_poly; push_cast; ring
    rw [hP_real] at hm
    -- Step 6.6: Use Real.sqrt_eq_cases to connect √P(n) = m to m² = P(n)
    rw [Real.sqrt_eq_cases] at hm
    rcases hm with ⟨hm_sq, hm_nn⟩ | ⟨hx_neg, hm_zero⟩
    · -- Step 6.6.1: Case m*m = P(n) with m ≥ 0 → conclude m² = P(n) as integers
      have hm_sq' : (m^2 : ℤ) = P_poly a b c n := by
        have h3 : ((m^2 : ℤ) : ℝ) = (m : ℝ) * (m : ℝ) := by push_cast; ring
        have h4 : ((m^2 : ℤ) : ℝ) = (P_poly a b c n : ℝ) := by rw [h3]; exact hm_sq
        exact Int.cast_injective h4
      exact hm_sq'
    · -- Step 6.6.2: Case P(n) < 0 - contradiction with P(n) > 0
      have hP_pos : (P_poly a b c n : ℝ) > 0 := Int.cast_pos.mpr hPn_pos
      linarith
