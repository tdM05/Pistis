import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators



/-Informal Statement

Suppose that $f(x)=\sum_{i=0}^{\infty} c_{i} x^{i}$ is a power series for which each coefficient $c_{i}$ is 0 or 1 . Show that if $f(2 / 3)=3 / 2$, then $f(1 / 2)$ must be irrational.
-/

/-Informal Proof

Suppose by way of contradiction that $f(1/2)$ is rational. Then $\sum_{i=0}^{\infty} c_i 2^{-i}$ is the binary expansion of a rational number, and hence must be eventually periodic; that is, there exist some integers $m,n$ such that
$c_i = c_{m+i}$ for all $i \geq n$. We may then write
\[
f(x) = \sum_{i=0}^{n-1} c_i x^i + \frac{x^n}{1-x^m} \sum_{i=0}^{m-1} c_{n+i} x^i.
\]
Evaluating at $x = 2/3$, we may equate $f(2/3) = 3/2$ with 
\[
\frac{1}{3^{n-1}} \sum_{i=0}^{n-1} c_i 2^i 3^{n-i-1} + \frac{2^n 3^m}{3^{n+m-1}(3^m-2^m)} \sum_{i=0}^{m-1} c_{n+i} 2^i 3^{m-1-i};
\]
since all terms on the right-hand side have odd denominator, the same must be true of the sum, a contradiction.
-/

/-
  ============================================================================
  Putnam 2017 B3: A challenging competition problem about power series
  ============================================================================

  Statement: If f(x) = Σ c_i * x^i where each c_i ∈ {0,1}, and f(2/3) = 3/2,
  then f(1/2) must be irrational.

  Proof Strategy (from the informal proof):
  1. Suppose for contradiction that f(1/2) is rational
  2. Since c_i ∈ {0,1}, the sum Σ c_i * (1/2)^i is a binary expansion
  3. The binary expansion of a rational number with digits in {0,1} is eventually periodic
     (This is a classical result using pigeonhole on "tail sums")
  4. An eventually periodic sequence gives f(x) = P(x) + x^N * Q(x)/(1-x^m) in closed form
  5. Evaluating at x = 2/3:
     - 1/(1-(2/3)^m) = 3^m/(3^m - 2^m)
     - 3^m - 2^m is always ODD for m ≥ 1 (since 3^m ≡ 1 (mod 2) and 2^m ≡ 0 (mod 2))
     - All denominators in the expression are powers of 3 and (3^m - 2^m), all odd
     - Hence f(2/3) has odd denominator (when reduced)
  6. But 3/2 has even denominator (namely 2), contradiction!
-/

-- ============================================================================
-- Helper Definitions and Lemmas
-- ============================================================================

/-- A sequence is eventually periodic if there exist N and m ≥ 1 such that
    c(N + m + k) = c(N + k) for all k ≥ 0 -/
def IsEventuallyPeriodic (c : ℕ → ℝ) : Prop :=
  ∃ N m : ℕ, m ≥ 1 ∧ ∀ k : ℕ, c (N + m + k) = c (N + k)

/-- The tail sum starting from position n: T_n = Σ_{i≥0} c_{n+i} * (1/2)^i -/
noncomputable def tailSum (c : ℕ → ℝ) (n : ℕ) : ℝ := ∑' (i : ℕ), c (n + i) * (1/2 : ℝ)^i

/-- Helper: 3^m - 2^m is odd for any m ≥ 1
    Proof: 3^m ≡ 1^m ≡ 1 (mod 2) and 2^m ≡ 0 (mod 2), so 3^m - 2^m ≡ 1 (mod 2) -/
lemma three_pow_sub_two_pow_odd (m : ℕ) (hm : m ≥ 1) : Odd (3^m - 2^m) := by
  -- Step 1: Establish 2^m < 3^m (needed for subtraction in ℕ)
  have h1 : 2^m < 3^m := Nat.pow_lt_pow_left (by norm_num : 2 < 3) (Nat.one_le_iff_ne_zero.mp hm)
  -- Step 2: Reduce to showing (3^m - 2^m) % 2 = 1
  rw [Nat.odd_iff]
  -- Step 3: 3^m ≡ 1 (mod 2) since 3 ≡ 1 (mod 2)
  have h3 : 3^m % 2 = 1 := by simp [Nat.pow_mod]
  -- Step 4: 2^m ≡ 0 (mod 2) since 2 | 2^m
  have h4 : 2^m % 2 = 0 := by
    have : (2 : ℕ) ∣ 2^m := dvd_pow_self 2 (Nat.one_le_iff_ne_zero.mp hm)
    exact Nat.mod_eq_zero_of_dvd this
  -- Step 5: Conclude by modular arithmetic
  omega

/-- The tail sum is summable for coefficients in {0,1} -/
lemma tailSum_summable (c : ℕ → ℝ) (hc : ∀ n, c n = 0 ∨ c n = 1) (n : ℕ) :
    Summable (fun i => c (n + i) * (1/2 : ℝ)^i) := by
  -- Step 1: Establish bounds on coefficients
  have hc_bounds : ∀ k, 0 ≤ c k ∧ c k ≤ 1 := fun k => by rcases hc k with h | h <;> simp [h]
  -- Step 2: Use comparison with geometric series
  have habs_half' : ‖|(1/2 : ℝ)|‖ < 1 := by simp; norm_num
  apply Summable.of_norm_bounded (g := fun i => |(1/2 : ℝ)|^i)
  · exact summable_geometric_of_abs_lt_one habs_half'
  · intro i
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    have h1 : |c (n+i)| ≤ 1 := by
      rw [abs_le]; constructor <;> [linarith [(hc_bounds (n+i)).1]; exact (hc_bounds (n+i)).2]
    calc |c (n+i)| * |(1/2 : ℝ)| ^ i ≤ 1 * |(1/2 : ℝ)| ^ i :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg (abs_nonneg _) i)
      _ = |(1/2 : ℝ)| ^ i := one_mul _

/-- The tail sum is nonnegative -/
lemma tailSum_nonneg (c : ℕ → ℝ) (hc : ∀ n, c n = 0 ∨ c n = 1) (n : ℕ) :
    0 ≤ tailSum c n := by
  unfold tailSum
  apply tsum_nonneg
  intro i
  rcases hc (n + i) with h | h <;> simp [h]

/-- The tail sum is at most 2 (sum of all 1's is exactly 2) -/
lemma tailSum_le_two (c : ℕ → ℝ) (hc : ∀ n, c n = 0 ∨ c n = 1) (n : ℕ) :
    tailSum c n ≤ 2 := by
  unfold tailSum
  calc ∑' (i : ℕ), c (n + i) * (1/2 : ℝ) ^ i
      ≤ ∑' (i : ℕ), (1 : ℝ) * (1/2 : ℝ) ^ i := by
        apply Summable.tsum_le_tsum
        · intro i; rcases hc (n + i) with h | h <;> simp [h]
        · exact tailSum_summable c hc n
        · simp only [one_mul]; exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
    _ = 2 := by
        simp only [one_mul]
        rw [tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)]
        norm_num

/-- 3/2 as a rational has denominator 2 (computed) -/
lemma rat_three_halves_den : (3/2 : ℚ).den = 2 := by native_decide

/-- 3/2 does not have odd denominator -/
lemma three_halves_den_not_odd : ¬ Odd (3/2 : ℚ).den := by
  rw [rat_three_halves_den]
  simp [Nat.odd_iff]

/-- A rational with odd denominator cannot equal 3/2 -/
lemma odd_denom_ne_three_halves (q : ℚ) (hodd : Odd q.den) : q ≠ 3/2 := by
  intro heq
  rw [heq] at hodd
  exact three_halves_den_not_odd hodd

/-- Any divisor of an odd number is odd -/
lemma odd_of_dvd_odd (a b : ℕ) (hb : Odd b) (ha : a ∣ b) : Odd a :=
  Odd.of_dvd_nat hb ha

/-- If we form A/B with B odd, the reduced denominator is odd -/
lemma divInt_den_odd_of_odd_denom (a : ℤ) (b : ℕ) (hb : Odd b) (_hb_pos : 0 < b) :
    Odd (Rat.divInt a b).den := by
  have h : ((Rat.divInt a b).den : ℤ) ∣ (b : ℤ) := Rat.den_dvd a b
  have h' : (Rat.divInt a b).den ∣ b := Int.ofNat_dvd.mp (by simpa using h)
  exact odd_of_dvd_odd _ _ hb h'

/-- No rational of the form A/B with B odd equals 3/2 -/
lemma no_odd_denom_eq_three_halves (A : ℤ) (B : ℕ) (hB : Odd B) (hB_pos : 0 < B) :
    Rat.divInt A B ≠ 3/2 := by
  intro heq
  have h1 : Odd (Rat.divInt A B).den := divInt_den_odd_of_odd_denom A B hB hB_pos
  rw [heq, rat_three_halves_den] at h1
  simp [Nat.odd_iff] at h1

/-- 3^n is odd -/
lemma three_pow_odd (n : ℕ) : Odd (3^n : ℕ) := Odd.pow (by decide : Odd (3 : ℕ))

/-- Product of odd numbers is odd -/
lemma odd_mul_odd (a b : ℕ) (ha : Odd a) (hb : Odd b) : Odd (a * b) := ha.mul hb

/-- 3^n * (3^m - 2^m) is odd for m ≥ 1 -/
lemma three_pow_mul_diff_odd (n m : ℕ) (hm : m ≥ 1) : Odd (3^n * (3^m - 2^m)) :=
  odd_mul_odd _ _ (three_pow_odd n) (three_pow_sub_two_pow_odd m hm)

-- ============================================================================
-- Additional Helper Lemmas for eventually_periodic_implies_odd_denom
-- ============================================================================

/-- Helper: 1 is odd -/
lemma one_odd : Odd (1 : ℕ) := ⟨0, rfl⟩

/-- (2/3)^n as a rational has odd denominator -/
lemma two_thirds_pow_odd_denom (n : ℕ) : Odd ((2/3 : ℚ)^n).den := by
  -- Step 1: Base case - (2/3)^0 = 1 has denominator 1 which is odd
  -- Step 2: Inductive step - (2/3)^(k+1).den divides (2/3)^k.den * 3, both odd
  induction n with
  | zero =>
    simp only [pow_zero]
    have h1 : (1 : ℚ).den = 1 := by native_decide
    rw [h1]
    exact one_odd
  | succ k ih =>
    rw [pow_succ]
    have h23 : (2/3 : ℚ).den = 3 := by native_decide
    have h1 : ((2/3 : ℚ)^k * (2/3 : ℚ)).den ∣ ((2/3 : ℚ)^k).den * (2/3 : ℚ).den :=
      Rat.mul_den_dvd ((2/3 : ℚ)^k) (2/3 : ℚ)
    rw [h23] at h1
    have h3_odd : Odd (3 : ℕ) := by decide
    have hprod_odd : Odd (((2/3 : ℚ)^k).den * 3) := ih.mul h3_odd
    exact Odd.of_dvd_nat hprod_odd h1

/-- A sum of rationals with 0-1 coefficients and base (2/3) has odd denominator -/
lemma sum_01_two_thirds_odd_denom (a : ℕ → ℚ) (ha : ∀ i, a i = 0 ∨ a i = 1) (n : ℕ) :
    Odd (∑ i ∈ Finset.range n, a i * (2/3 : ℚ)^i).den := by
  -- Proof by induction on n
  -- Base case: empty sum has denominator 1 (odd)
  -- Inductive step: sum.den divides product of odd denominators, hence odd
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    have h0 : (0 : ℚ).den = 1 := by native_decide
    rw [h0]
    exact one_odd
  | succ k ih =>
    rw [Finset.sum_range_succ]
    rcases ha k with hk0 | hk1
    · simp only [hk0, zero_mul, add_zero]
      exact ih
    · simp only [hk1, one_mul]
      have h1 : Odd ((2/3 : ℚ)^k).den := two_thirds_pow_odd_denom k
      have h2 : (∑ i ∈ Finset.range k, a i * (2/3 : ℚ)^i + (2/3 : ℚ)^k).den ∣
                (∑ i ∈ Finset.range k, a i * (2/3 : ℚ)^i).den * ((2/3 : ℚ)^k).den :=
        Rat.add_den_dvd _ _
      have hprod_odd : Odd ((∑ i ∈ Finset.range k, a i * (2/3 : ℚ)^i).den * ((2/3 : ℚ)^k).den) :=
        ih.mul h1
      exact Odd.of_dvd_nat hprod_odd h2

/-- The denominator of a * b * c divides denom(a) * denom(b) * denom(c) -/
lemma mul_mul_den_dvd (a b c : ℚ) : (a * b * c).den ∣ a.den * b.den * c.den := by
  have h1 : (a * b).den ∣ a.den * b.den := Rat.mul_den_dvd a b
  have h2 : (a * b * c).den ∣ (a * b).den * c.den := Rat.mul_den_dvd (a * b) c
  calc (a * b * c).den ∣ (a * b).den * c.den := h2
    _ ∣ (a.den * b.den) * c.den := Nat.mul_dvd_mul_right h1 c.den
    _ = a.den * b.den * c.den := by ring

/-- The series Σ c_i * x^i converges for |x| < 1 -/
lemma series_summable (c : ℕ → ℝ) (hc : ∀ n, c n = 0 ∨ c n = 1) (x : ℝ) (hx : |x| < 1) :
    Summable (fun i => c i * x^i) := by
  -- Proof: Compare with geometric series |x|^i which converges for |x| < 1
  have hc_bounds : ∀ k, |c k| ≤ 1 := fun k => by rcases hc k with h | h <;> simp [h]
  apply Summable.of_norm_bounded (g := fun i => |x|^i)
  · have habs : |(|x|)| < 1 := by simp [hx]
    exact summable_geometric_of_abs_lt_one habs
  · intro i
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    calc |c i| * |x|^i ≤ 1 * |x|^i := by
          apply mul_le_mul_of_nonneg_right (hc_bounds i)
          exact pow_nonneg (abs_nonneg _) i
      _ = |x|^i := one_mul _

/-- The series at x = 2/3 converges -/
lemma series_summable_at_two_thirds (c : ℕ → ℝ) (hc : ∀ n, c n = 0 ∨ c n = 1) :
    Summable (fun i => c i * (2/3 : ℝ)^i) := by
  apply series_summable c hc
  norm_num

/-- For nonzero q, q⁻¹.den divides q.num.natAbs -/
lemma rat_inv_den_dvd_num (q : ℚ) (hq : q ≠ 0) : q⁻¹.den ∣ q.num.natAbs := by
  -- q⁻¹ = q.den / q.num, so q⁻¹.den divides q.num by Rat.den_dvd
  rw [Rat.inv_def]
  have hnum_ne : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have h3 := Rat.den_dvd q.den q.num
  have h6 : ((Rat.divInt q.den q.num).den : ℤ) ∣ q.num := h3
  have h7 : (Rat.divInt q.den q.num).den ∣ q.num.natAbs := by
    have := Int.natCast_dvd.mp (Int.dvd_natAbs.mpr h6)
    exact this
  exact h7

/-- The numerator of (1 - (2/3)^m) is odd for m ≥ 1 -/
lemma one_sub_two_thirds_pow_num_odd (m : ℕ) (hm : m ≥ 1) :
    Odd ((1 - (2/3 : ℚ)^m).num).natAbs := by
  -- Step 1: (1 - (2/3)^m) = (3^m - 2^m) / 3^m
  -- Step 2: The numerator divides 3^m - 2^m which is odd
  have h_lt : 2^m < 3^m := Nat.pow_lt_pow_left (by norm_num : 2 < 3) (Nat.one_le_iff_ne_zero.mp hm)
  have h_le : 2^m ≤ 3^m := le_of_lt h_lt

  have h3_ne : (3 : ℚ)^m ≠ 0 := pow_ne_zero m (by norm_num)
  have h_pow : (2/3 : ℚ)^m = (2 : ℚ)^m / (3 : ℚ)^m := by rw [div_pow]

  -- 3^m - 2^m is odd (since 3^m ≡ 1 mod 2 and 2^m ≡ 0 mod 2)
  have h_diff_odd : Odd (3^m - 2^m : ℕ) := by
    rw [Nat.odd_iff]
    have h3 : 3^m % 2 = 1 := by simp [Nat.pow_mod]
    have h4 : 2^m % 2 = 0 := by
      have : (2 : ℕ) ∣ 2^m := dvd_pow_self 2 (Nat.one_le_iff_ne_zero.mp hm)
      exact Nat.mod_eq_zero_of_dvd this
    omega

  -- The numerator of (1 - (2/3)^m) divides 3^m - 2^m
  have h_dvd : ((1 - (2/3 : ℚ)^m).num).natAbs ∣ (3^m - 2^m) := by
    have h_val : (1 - (2/3 : ℚ)^m) = Rat.divInt ((3^m : ℤ) - (2^m : ℤ)) (3^m) := by
      rw [h_pow]
      have h_eq1 : (1 : ℚ) - (2 : ℚ)^m / (3 : ℚ)^m = ((3 : ℚ)^m - (2 : ℚ)^m) / (3 : ℚ)^m := by
        field_simp
      rw [h_eq1]
      rw [Rat.divInt_eq_div]
      congr 1
      · push_cast; ring
      · push_cast; rfl
    rw [h_val]
    have h3m_pos : (0 : ℤ) < (3^m : ℕ) := by positivity
    have h3m_ne : ((3^m : ℕ) : ℤ) ≠ 0 := ne_of_gt h3m_pos
    have h_num := Rat.num_dvd ((3^m : ℤ) - (2^m : ℤ)) h3m_ne
    have h1 := Int.natAbs_dvd_natAbs.mpr h_num
    have h2 : ((3^m : ℤ) - (2^m : ℤ)).natAbs = 3^m - 2^m := by
      have h3 : (3^m : ℤ) - (2^m : ℤ) = ((3^m - 2^m : ℕ) : ℤ) := by
        rw [Int.ofNat_sub h_le]
        push_cast
        ring
      rw [h3]
      simp only [Int.natAbs_natCast]
    rw [h2] at h1
    have h4 : Rat.divInt ((3^m : ℤ) - (2^m : ℤ)) ((3^m : ℕ) : ℤ) =
              Rat.divInt ((3^m : ℤ) - (2^m : ℤ)) (3^m : ℤ) := by
      congr 1
    rw [h4] at h1
    exact h1

  exact Odd.of_dvd_nat h_diff_odd h_dvd

/-- The inverse of (1 - (2/3)^m) has odd denominator for m ≥ 1 -/
lemma inv_one_sub_two_thirds_pow_odd_denom (m : ℕ) (hm : m ≥ 1) :
    Odd ((1 - (2/3 : ℚ)^m)⁻¹).den := by
  -- Step 1: (1 - (2/3)^m) is nonzero since (2/3)^m < 1
  have h_ne : (1 - (2/3 : ℚ)^m) ≠ 0 := by
    have h1 : (2/3 : ℚ)^m < 1 := by
      have : (2/3 : ℚ) < 1 := by norm_num
      exact pow_lt_one₀ (by norm_num) this (Nat.one_le_iff_ne_zero.mp hm)
    linarith
  -- Step 2: The inverse's denominator divides the numerator (which is odd)
  have h_den_dvd := rat_inv_den_dvd_num (1 - (2/3 : ℚ)^m) h_ne
  have h_num_odd := one_sub_two_thirds_pow_num_odd m hm
  exact Odd.of_dvd_nat h_num_odd h_den_dvd

/-- 1 - (2/3)^m = (3^m - 2^m)/3^m -/
lemma one_sub_two_thirds_pow (m : ℕ) : 1 - (2/3 : ℝ)^m = ((3:ℝ)^m - (2:ℝ)^m) / (3:ℝ)^m := by
  have h3 : (3 : ℝ)^m ≠ 0 := pow_ne_zero m (by norm_num)
  have h1 : (2/3 : ℝ)^m = (2:ℝ)^m / (3:ℝ)^m := by rw [div_pow]
  rw [h1]
  field_simp

/-- 1/(1-(2/3)^m) = 3^m/(3^m - 2^m) for m ≥ 1 -/
lemma inv_one_sub_two_thirds_pow (m : ℕ) (hm : m ≥ 1) :
    (1 - (2/3 : ℝ)^m)⁻¹ = (3:ℝ)^m / ((3:ℝ)^m - (2:ℝ)^m) := by
  have h3m : (3 : ℝ)^m ≠ 0 := pow_ne_zero m (by norm_num)
  have h32_nat : 2^m < 3^m := Nat.pow_lt_pow_left (by norm_num : 2 < 3) (Nat.one_le_iff_ne_zero.mp hm)
  have h32 : (3 : ℝ)^m - (2 : ℝ)^m ≠ 0 := by
    have : (2 : ℝ)^m < (3 : ℝ)^m := by norm_cast
    linarith
  rw [one_sub_two_thirds_pow]
  field_simp

/-- Key recurrence: T_n = c_n + (1/2) * T_{n+1} -/
lemma tailSum_recurrence (c : ℕ → ℝ) (hc : ∀ n, c n = 0 ∨ c n = 1) (n : ℕ) :
    tailSum c n = c n + (1/2) * tailSum c (n + 1) := by
  unfold tailSum
  rw [Summable.tsum_eq_zero_add (tailSum_summable c hc n)]
  simp only [add_zero, pow_zero, mul_one]
  congr 1
  have heq : (fun i => c (n + (i + 1)) * (1/2 : ℝ)^(i+1)) =
             (fun i => (1/2 : ℝ) * (c (n + 1 + i) * (1/2 : ℝ)^i)) := by
    ext i
    have hi : n + (i + 1) = n + 1 + i := by omega
    rw [hi, pow_succ' (1/2 : ℝ) i]
    ring
  rw [heq, tsum_mul_left]

/-- Rearranged recurrence: T_{n+1} = 2*(T_n - c_n) -/
lemma tailSum_succ (c : ℕ → ℝ) (hc : ∀ n, c n = 0 ∨ c n = 1) (n : ℕ) :
    tailSum c (n + 1) = 2 * (tailSum c n - c n) := by
  linarith [tailSum_recurrence c hc n]

-- ============================================================================
-- Key Lemmas (require substantial development to prove fully)
-- ============================================================================

/-- KEY LEMMA 1: If Σ c_i * (1/2)^i is rational with c_i ∈ {0,1}, then c is eventually periodic.

    Proof sketch:
    - Define T_n = Σ_{i≥0} c_{n+i} * (1/2)^i (tail sum starting at position n)
    - Key recurrence: T_{n+1} = 2*(T_n - c_n)
    - If T_0 = p/q is rational, then each T_n has the form (integer)/(power of 2 × q)
    - Since T_n ∈ [0, 2) and has bounded denominator, T_n takes only finitely many values
    - By pigeonhole, T_{n1} = T_{n2} for some n1 < n2
    - Since the binary expansion with {0,1} digits is unique, c_{n1+k} = c_{n2+k} for all k
    - This gives periodicity with period m = n2 - n1
-/
lemma rational_implies_eventually_periodic (c : ℕ → ℝ) (hc : ∀ n, c n = 0 ∨ c n = 1)
    (p : ℤ) (q : ℕ) (hq : q ≥ 1)
    (hrat : ∑' (i : ℕ), c i * (1/2 : ℝ)^i = p / q) : IsEventuallyPeriodic c := by
  /-
    ==========================================================================
    PROOF OF KEY LEMMA 1: Rational binary expansion implies eventually periodic
    ==========================================================================

    Step 1: Define the tail sums T_n = Σ_{i≥0} c_{n+i} * (1/2)^i
    Step 2: Show T_0 = p/q (the original sum)
    Step 3: Show T_{n+1} = 2*(T_n - c_n) (recurrence relation)
    Step 4: Prove T_n has denominator dividing q
    Step 5: Since T_n ∈ [0, 2] with denom | q, T_n ∈ {0/q, 1/q, ..., 2q/q}
    Step 6: Consider pairs (T_rat n, c_rat n) to handle T_n = 1 case
    Step 7: Pigeonhole: among 4q+3 pairs, two must be equal
    Step 8: Equal pairs propagate forward, giving periodicity
  -/

  -- Step 1: The tail sum at 0 equals the original sum
  -- Step 1.1: Show tailSum c 0 = ∑' (i : ℕ), c i * (1/2)^i
  have htail0 : tailSum c 0 = ∑' (i : ℕ), c i * (1/2 : ℝ)^i := by
    unfold tailSum; simp only [zero_add]

  -- Step 1.2: So tailSum c 0 = p/q
  have htail0_eq : tailSum c 0 = p / q := by rw [htail0, hrat]

  -- Step 2: Define rational coefficients
  -- Step 2.1: c i as a rational (0 or 1)
  let c_rat : ℕ → ℚ := fun i => if c i = 1 then 1 else 0

  -- Step 2.2: c_rat takes values in {0, 1}
  have hc_rat_01 : ∀ i, c_rat i = 0 ∨ c_rat i = 1 := fun i => by
    simp only [c_rat]; by_cases h : c i = 1 <;> simp [h]

  -- Step 2.3: c_rat cast to ℝ equals c
  have hc_rat_cast : ∀ i, (c_rat i : ℝ) = c i := fun i => by
    simp only [c_rat]; rcases hc i with hi | hi <;> simp [hi]

  -- Step 3: Define rational tail sum T_rat by recursion
  -- Step 3.1: Use choose to get a function satisfying the recurrence
  have hT_rat_exists : ∃ T_rat : ℕ → ℚ,
      T_rat 0 = p / q ∧ ∀ n, T_rat (n + 1) = 2 * (T_rat n - c_rat n) := by
    use fun n => Nat.rec (p / q) (fun k T_k => 2 * (T_k - c_rat k)) n
    exact ⟨rfl, fun _ => rfl⟩
  obtain ⟨T_rat, hT_rat_0, hT_rat_succ⟩ := hT_rat_exists

  -- Step 4: Show (T_rat n : ℝ) = tailSum c n by induction
  have hT_rat_eq_tailSum : ∀ n, (T_rat n : ℝ) = tailSum c n := by
    intro n
    induction n with
    | zero =>
      -- Step 4.1 Base case: T_rat 0 = p/q and tailSum c 0 = p/q
      rw [hT_rat_0, htail0_eq]
      simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
    | succ k ih =>
      -- Step 4.2: Inductive case
      rw [hT_rat_succ k, Rat.cast_mul, Rat.cast_sub, Rat.cast_ofNat]
      rw [ih, hc_rat_cast k, tailSum_succ c hc k]

  -- Step 5: Bounds on T_rat n
  -- Step 5.1: T_rat n ≥ 0
  have hT_rat_nonneg : ∀ n, 0 ≤ T_rat n := by
    intro n
    have h : (0 : ℝ) ≤ (T_rat n : ℝ) := by
      rw [hT_rat_eq_tailSum n]; exact tailSum_nonneg c hc n
    exact Rat.cast_nonneg.mp h

  -- Step 5.2: T_rat n ≤ 2
  have hT_rat_le_2 : ∀ n, T_rat n ≤ 2 := by
    intro n
    have h : (T_rat n : ℝ) ≤ (2 : ℝ) := by
      rw [hT_rat_eq_tailSum n]; exact tailSum_le_two c hc n
    exact_mod_cast h

  -- Step 6: Denominator of T_rat n divides q
  -- Step 6.1: Prove by induction
  have hT_rat_den_dvd_q : ∀ n, (T_rat n).den ∣ q := by
    intro n
    induction n with
    | zero =>
      -- Step 6.1.1: T_rat 0 = p/q, so denominator divides q
      rw [hT_rat_0]
      -- (p / q).den divides q by Rat.den_dvd
      have hq_pos : 0 < (q : ℤ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hq
      have h := Rat.den_dvd p q
      have h' : ((p : ℚ) / q).den ∣ q := by
        have heq : (p : ℚ) / q = Rat.divInt p q := by simp [Rat.divInt_eq_div]
        rw [heq]
        exact Int.ofNat_dvd.mp (by simpa using h)
      exact h'
    | succ k ih =>
      -- Step 6.1.2: T_rat (k+1) = 2 * (T_rat k - c_rat k)
      rw [hT_rat_succ k]
      -- (2 * r).den divides r.den for any r
      have h1 : (2 * (T_rat k - c_rat k)).den ∣ (T_rat k - c_rat k).den := by
        have h2 : (2 : ℚ).den = 1 := rfl
        have h3 : (2 * (T_rat k - c_rat k)).den ∣ (2 : ℚ).den * (T_rat k - c_rat k).den :=
          Rat.mul_den_dvd 2 (T_rat k - c_rat k)
        simp only [h2, one_mul] at h3
        exact h3
      -- (T_rat k - c_rat k).den divides T_rat k.den * c_rat k.den
      have h4 : (T_rat k - c_rat k).den ∣ (T_rat k).den * (c_rat k).den :=
        Rat.sub_den_dvd (T_rat k) (c_rat k)
      -- c_rat k ∈ {0, 1}, so c_rat k.den = 1
      have h5 : (c_rat k).den = 1 := by
        rcases hc_rat_01 k with h | h <;> simp [h]
      -- So (T_rat k - c_rat k).den divides T_rat k.den
      have h6 : (T_rat k - c_rat k).den ∣ (T_rat k).den := by
        calc (T_rat k - c_rat k).den ∣ (T_rat k).den * (c_rat k).den := h4
          _ = (T_rat k).den * 1 := by rw [h5]
          _ = (T_rat k).den := mul_one _
      -- Combine
      calc (2 * (T_rat k - c_rat k)).den ∣ (T_rat k - c_rat k).den := h1
        _ ∣ (T_rat k).den := h6
        _ ∣ q := ih

  -- Step 7: T_rat n is in {m/q : m ∈ ℤ, 0 ≤ m/q ≤ 2} = {0/q, 1/q, ..., 2q/q}
  -- So there are at most 2*q + 1 possible values for T_rat n.

  -- Step 7.1: T_rat n * q is an integer in [0, 2*q]
  have hT_rat_times_q_int : ∀ n, ∃ m : ℤ, T_rat n = m / q ∧ 0 ≤ m ∧ m ≤ 2 * q := by
    intro n
    have hdvd_n : (T_rat n).den ∣ q := hT_rat_den_dvd_q n
    -- T_rat n = (T_rat n).num / (T_rat n).den
    -- Since (T_rat n).den | q, let q = (T_rat n).den * k for some k
    obtain ⟨k, hk⟩ := hdvd_n
    -- T_rat n = (T_rat n).num / (T_rat n).den = ((T_rat n).num * k) / q
    use (T_rat n).num * k
    have hden_pos : (T_rat n).den > 0 := (T_rat n).den_pos
    have hq_pos : q > 0 := Nat.lt_of_lt_of_le Nat.zero_lt_one hq
    have hq_ge : q ≥ (T_rat n).den := Nat.le_of_dvd hq_pos (hT_rat_den_dvd_q n)
    have hk_pos : k ≥ 1 := by
      have hden_pos' : (T_rat n).den ≥ 1 := Nat.one_le_iff_ne_zero.mpr (ne_of_gt hden_pos)
      have hk_eq : (T_rat n).den * k = q := hk.symm
      by_contra hk_zero
      push_neg at hk_zero
      have hk_eq_0 : k = 0 := Nat.lt_one_iff.mp hk_zero
      rw [hk_eq_0, mul_zero] at hk_eq
      omega
    constructor
    · -- Step 7.1.1: T_rat n = ((T_rat n).num * k) / q
      have h1 : (T_rat n : ℚ) = (T_rat n).num / (T_rat n).den := (Rat.num_div_den (T_rat n)).symm
      conv_lhs => rw [h1]
      have hden_ne : ((T_rat n).den : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hden_pos
      have hq_ne : (q : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hq_pos
      rw [hk]; field_simp; push_cast; ring
    constructor
    · -- Step 7.1.2: 0 ≤ (T_rat n).num * k
      have h1 : 0 ≤ (T_rat n).num := Rat.num_nonneg.mpr (hT_rat_nonneg n)
      have h2 : 0 ≤ (k : ℤ) := Int.natCast_nonneg k
      exact mul_nonneg h1 h2
    · -- Step 7.1.3: (T_rat n).num * k ≤ 2 * q
      have hle : T_rat n ≤ 2 := hT_rat_le_2 n
      have h1 : (T_rat n).num ≤ 2 * (T_rat n).den := by
        have hden_pos' : (0 : ℚ) < (T_rat n).den := by exact_mod_cast hden_pos
        have hden_ne : ((T_rat n).den : ℚ) ≠ 0 := ne_of_gt hden_pos'
        -- T_rat n = num / den, so num = T_rat n * den
        have h_num_eq : ((T_rat n).num : ℚ) = (T_rat n : ℚ) * (T_rat n).den := by
          have := Rat.num_div_den (T_rat n)
          field_simp at this ⊢
          linarith [this]
        have h_ineq : ((T_rat n).num : ℚ) ≤ 2 * (T_rat n).den :=
          calc ((T_rat n).num : ℚ) = (T_rat n : ℚ) * (T_rat n).den := h_num_eq
            _ ≤ 2 * (T_rat n).den := mul_le_mul_of_nonneg_right hle (le_of_lt hden_pos')
        exact_mod_cast h_ineq
      have h2 : 0 ≤ (k : ℤ) := Int.natCast_nonneg k
      have h3 : (T_rat n).num * k ≤ (2 * (T_rat n).den) * k := mul_le_mul_of_nonneg_right h1 h2
      calc (T_rat n).num * k ≤ (2 * (T_rat n).den) * k := h3
        _ = 2 * ((T_rat n).den : ℤ) * (k : ℤ) := by ring
        _ = 2 * q := by simp only [hk, Nat.cast_mul]; ring

  -- Step 8: Pigeonhole principle
  -- Consider T_rat 0, T_rat 1, ..., T_rat (2*q).
  -- These are 2*q + 1 values, each of the form m/q with m ∈ {0, 1, ..., 2*q}.
  -- There are only 2*q + 1 such values, so if all are distinct, they exhaust
  -- {0/q, 1/q, ..., 2q/q}. But then we can use the periodicity argument.
  -- Actually, we need: two of them are equal.

  -- Step 8.1: If all T_rat 0, ..., T_rat (2*q) are distinct, they form a bijection
  --           with {0, 1, ..., 2*q}/q. Check if this leads to contradiction or periodicity.

  -- Step 8.2: Alternative: Use pigeonhole on a slightly larger range.
  -- Consider T_rat 0, ..., T_rat (2*q + 1). These are 2*q + 2 values.
  -- Each is in {0/q, ..., 2q/q}, which has 2*q + 1 elements.
  -- By pigeonhole, at least two are equal.

  -- Step 8.3: Actually, we need the sequence to eventually be periodic.
  -- The key: once T_rat n1 = T_rat n2 for n1 < n2, we get periodicity.
  -- Let's prove: there exist n1 < n2 with T_rat n1 = T_rat n2.

  -- Step 8.4: Define the map from {0, ..., 2*q+1} to {m/q : 0 ≤ m ≤ 2*q}
  -- Use Finset.exists_ne_map_eq_of_card_lt_of_maps_to

  -- Step 8.1: Define target set of possible T_rat values
  let target : Finset ℚ := (Finset.range (2 * q + 1)).image (fun m : ℕ => (m : ℚ) / q)

  have htarget_card : target.card ≤ 2 * q + 1 := by
    calc target.card ≤ (Finset.range (2 * q + 1)).card := Finset.card_image_le
      _ = 2 * q + 1 := Finset.card_range _

  -- Step 8.2: T_rat n is in target for all n
  have hT_rat_in_target : ∀ n, T_rat n ∈ target := by
    intro n
    obtain ⟨m, hm_eq, hm_ge, hm_le⟩ := hT_rat_times_q_int n
    simp only [target, Finset.mem_image, Finset.mem_range]
    use m.toNat
    constructor
    · -- m.toNat < 2 * q + 1
      have hm_nat : m = m.toNat := (Int.toNat_of_nonneg hm_ge).symm
      have hm_le_nat : m.toNat ≤ 2 * q := by
        have h1 : m ≤ 2 * (q : ℤ) := hm_le
        have h2 : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm_ge
        have h3 : (m.toNat : ℤ) ≤ 2 * q := by rw [h2]; exact h1
        omega
      omega
    · -- T_rat n = m.toNat / q
      have hm_nat : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm_ge
      rw [hm_eq]
      congr 1
      have : (m.toNat : ℚ) = m := by exact_mod_cast hm_nat
      exact this

  -- Step 8.5: Consider 2*q + 2 values
  -- If we look at T_rat 0, ..., T_rat (2*q+1), that's 2*q+2 values
  -- mapping into target which has ≤ 2*q+1 elements.

  -- But actually we need to be more careful. Let's use a cleaner approach:
  -- The set {T_rat n : n ∈ ℕ} is a subset of target (finite).
  -- Since T_rat : ℕ → ℚ and the range is finite, by pigeonhole,
  -- T_rat is not injective on some finite prefix.

  -- Step 8.6: There exist n1 < n2 ≤ 2*q+1 such that T_rat n1 = T_rat n2
  obtain ⟨n1, hn1, n2, hn2, hne, heq⟩ : ∃ n1 ∈ Finset.range (2 * q + 2),
      ∃ n2 ∈ Finset.range (2 * q + 2), n1 ≠ n2 ∧ T_rat n1 = T_rat n2 := by
    have hcard_source : (Finset.range (2 * q + 2)).card = 2 * q + 2 := Finset.card_range _
    have hcard_target : target.card ≤ 2 * q + 1 := htarget_card
    have hcard_lt : target.card < (Finset.range (2 * q + 2)).card := by
      rw [hcard_source]
      omega
    have hmaps : Set.MapsTo T_rat (↑(Finset.range (2 * q + 2))) (↑target) := by
      intro n _
      exact hT_rat_in_target n
    exact Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard_lt hmaps

  -- Step 8.7: WLOG n1 < n2
  have hn1_lt_n2_or_n2_lt_n1 : n1 < n2 ∨ n2 < n1 := hne.lt_or_gt
  obtain ⟨N, M, hNM, hTeq⟩ : ∃ N M : ℕ, N < M ∧ T_rat N = T_rat M := by
    rcases hn1_lt_n2_or_n2_lt_n1 with h | h
    · exact ⟨n1, n2, h, heq⟩
    · exact ⟨n2, n1, h, heq.symm⟩

  -- Step 9: T_rat N = T_rat M implies c_{N+k} = c_{M+k} for all k
  -- This is because the recurrence T_{n+1} = 2*(T_n - c_n) uniquely determines c_n from T_n and T_{n+1}.
  -- Actually: c_n = 0 iff T_n < 1, and c_n = 1 iff T_n ≥ 1 (since T_n ∈ [0, 2) and c_n ∈ {0, 1})
  -- Wait, that's only for T_n ∈ [0, 2). Let me reconsider.

  -- Step 9.1: From the recurrence: T_{n+1} = 2*(T_n - c_n), so c_n = T_n - T_{n+1}/2.
  -- Since c_n ∈ {0, 1}, we have:
  --   c_n = 0 iff T_{n+1} = 2*T_n
  --   c_n = 1 iff T_{n+1} = 2*T_n - 2

  -- Step 9.2: Key: c_n is determined by T_n, specifically:
  --   If T_n < 1, then c_n = 0 (and T_{n+1} = 2*T_n ∈ [0, 2))
  --   If T_n ≥ 1, then c_n = 1 (and T_{n+1} = 2*(T_n - 1) = 2*T_n - 2 ∈ [0, 2))
  -- This is because T_{n+1} must be in [0, 2), and only one choice of c_n achieves this.

  -- Note: The lemma `hc_determined` is not actually needed for the main proof.
  -- We use the pair (T_rat n, c_rat n) approach instead, which avoids needing
  -- to show c_n is uniquely determined by T_n (which fails at T_n = 1).

  -- Step 9.3: If T_rat N = T_rat M and c_rat N = c_rat M, then by recurrence,
  --           T_rat (N+k) = T_rat (M+k) and c_rat (N+k) = c_rat (M+k) for all k ≥ 0.

  -- But we might not have c_rat N = c_rat M from T_rat N = T_rat M alone.
  -- Let's use the pair approach.

  -- Step 10: Pairs (T_rat n, c_rat n)
  -- The pair takes values in a finite set.
  -- c_rat n ∈ {0, 1}, and T_rat n ∈ {0/q, 1/q, ..., 2q/q}.
  -- But c_rat n = 0 requires T_rat n ≤ 1, and c_rat n = 1 requires T_rat n ≥ 1.
  -- So valid pairs: {(m/q, 0) : 0 ≤ m ≤ q} ∪ {(m/q, 1) : q ≤ m ≤ 2q}.
  -- The overlap is (q/q, 0) and (q/q, 1), i.e., (1, 0) and (1, 1).
  -- Total pairs: (q+1) + (q+1) = 2q + 2.

  -- Actually, let's just count all pairs (T, c) where T ∈ target and c ∈ {0, 1}.
  -- That's at most (2q+1) * 2 = 4q+2 pairs.

  -- Step 10.1: Define the pair map
  let pair_map : ℕ → ℚ × ℚ := fun n => (T_rat n, c_rat n)

  -- Step 10.2: The pair takes values in a finite set
  let pair_target : Finset (ℚ × ℚ) := target ×ˢ ({0, 1} : Finset ℚ)

  have hpair_card : pair_target.card ≤ (2 * q + 1) * 2 := by
    have hcard_eq : pair_target.card = target.card * ({0, 1} : Finset ℚ).card := Finset.card_product target {0, 1}
    have h1 : ({0, 1} : Finset ℚ).card = 2 := by decide
    rw [hcard_eq, h1]
    exact Nat.mul_le_mul_right 2 htarget_card

  have hpair_in_target : ∀ n, pair_map n ∈ pair_target := by
    intro n
    simp only [pair_map, pair_target, Finset.mem_product]
    constructor
    · exact hT_rat_in_target n
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hc_rat_01 n with h | h <;> simp [h]

  -- Step 10.3: Pigeonhole on pairs
  -- Looking at (4q+3) pairs, we get a collision since (4q+3) > (2q+1)*2 = 4q+2.
  obtain ⟨n1', hn1', n2', hn2', hne', heq'⟩ : ∃ n1' ∈ Finset.range (4 * q + 3),
      ∃ n2' ∈ Finset.range (4 * q + 3), n1' ≠ n2' ∧ pair_map n1' = pair_map n2' := by
    have hcard_source : (Finset.range (4 * q + 3)).card = 4 * q + 3 := Finset.card_range _
    have hcard_target' : pair_target.card ≤ (2 * q + 1) * 2 := hpair_card
    have hcard_lt' : pair_target.card < (Finset.range (4 * q + 3)).card := by
      rw [hcard_source]
      calc pair_target.card ≤ (2 * q + 1) * 2 := hcard_target'
        _ = 4 * q + 2 := by ring
        _ < 4 * q + 3 := by omega
    have hmaps' : Set.MapsTo pair_map (↑(Finset.range (4 * q + 3))) (↑pair_target) := by
      intro n _
      exact hpair_in_target n
    exact Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard_lt' hmaps'

  -- Step 10.4: WLOG n1' < n2'
  obtain ⟨N', M', hNM', hpair_eq⟩ : ∃ N' M' : ℕ, N' < M' ∧ pair_map N' = pair_map M' := by
    have h : n1' < n2' ∨ n2' < n1' := hne'.lt_or_gt
    rcases h with h | h
    · exact ⟨n1', n2', h, heq'⟩
    · exact ⟨n2', n1', h, heq'.symm⟩

  -- Step 10.5: From pair_map N' = pair_map M', we get T_rat N' = T_rat M' and c_rat N' = c_rat M'
  have hTeq' : T_rat N' = T_rat M' := by
    have : (T_rat N', c_rat N') = (T_rat M', c_rat M') := hpair_eq
    exact Prod.mk.inj this |>.1
  have hceq' : c_rat N' = c_rat M' := by
    have : (T_rat N', c_rat N') = (T_rat M', c_rat M') := hpair_eq
    exact Prod.mk.inj this |>.2

  -- Step 11: By induction, c (N' + k) = c (M' + k) for all k ≥ 0
  -- Actually, we'll show c_rat (N' + k) = c_rat (M' + k), which implies c (N' + k) = c (M' + k).

  have hperiod : ∀ k : ℕ, c (N' + k) = c (M' + k) := by
    intro k
    -- We prove by induction that T_rat (N' + k) = T_rat (M' + k) and c_rat (N' + k) = c_rat (M' + k).
    have hinduction : ∀ j : ℕ, T_rat (N' + j) = T_rat (M' + j) ∧ c_rat (N' + j) = c_rat (M' + j) := by
      intro j
      induction j with
      | zero => simp only [add_zero]; exact ⟨hTeq', hceq'⟩
      | succ i ih =>
        obtain ⟨hT_ih, hc_ih⟩ := ih
        constructor
        · -- T_rat (N' + (i + 1)) = T_rat (M' + (i + 1))
          have heq1 : N' + (i + 1) = N' + i + 1 := by ring
          have heq2 : M' + (i + 1) = M' + i + 1 := by ring
          rw [heq1, heq2]
          have h1 : T_rat (N' + i + 1) = 2 * (T_rat (N' + i) - c_rat (N' + i)) := by
            have := hT_rat_succ (N' + i)
            convert this using 2
          have h2 : T_rat (M' + i + 1) = 2 * (T_rat (M' + i) - c_rat (M' + i)) := by
            have := hT_rat_succ (M' + i)
            convert this using 2
          rw [h1, h2, hT_ih, hc_ih]
        · -- c_rat (N' + i + 1) = c_rat (M' + i + 1)
          -- c_rat is determined by T_rat via the "if T < 1 then 0 else 1" rule,
          -- but with the complication at T = 1.
          -- However, since T_rat (N' + i + 1) = T_rat (M' + i + 1) (just proved above),
          -- and c_rat is part of a fixed sequence c,
          -- we use: c_rat n = if c n = 1 then 1 else 0.
          -- So c_rat (N' + i + 1) = c_rat (M' + i + 1) iff c (N' + i + 1) = c (M' + i + 1).

          -- From tailSum c (N' + i + 1) = tailSum c (M' + i + 1) (since T_rat agrees),
          -- we want to conclude c (N' + i + 1) = c (M' + i + 1).

          -- Key fact: If Σ_{j≥0} a_j * (1/2)^j = Σ_{j≥0} b_j * (1/2)^j with a_j, b_j ∈ {0, 1},
          -- and a_0 ≠ b_0, then the sums are DIFFERENT (unless we're at a dyadic rational).

          -- More precisely: if a_0 = 1 and b_0 = 0, then
          --   Σ a_j * (1/2)^j = 1 + Σ_{j≥1} a_j * (1/2)^j ≥ 1
          --   Σ b_j * (1/2)^j = 0 + Σ_{j≥1} b_j * (1/2)^j ≤ 0 + Σ_{j≥1} (1/2)^j = 1
          -- So if the sums are equal, they're both = 1, a boundary case.

          -- In that boundary case, a_0 = 1 with tail sum 0, or a_0 = 0 with tail sum 1.
          -- a_0 = 1, Σ_{j≥1} a_j * (1/2)^j = 0 means a_j = 0 for j ≥ 1.
          -- a_0 = 0, Σ_{j≥1} a_j * (1/2)^j = 1 means the tail has total sum 1,
          --   which can be achieved as (1, 0, 0, ...) shifted, i.e., a_1 = 1, a_j = 0 for j ≥ 2.
          --   Or as (0, 1, 1, 1, ...) shifted, i.e., a_j = 1 for j ≥ 1.

          -- For our sequences, both (c_{N'+i+1+j})_j and (c_{M'+i+1+j})_j are tails of c.
          -- They have the same sum. If their first terms differ, they're both representations of 1.
          -- But then the NEXT terms must be as above, and we can trace through.

          -- This is getting complicated. Let me use a different argument.

          -- Since c is fixed, and T_rat (N' + i + 1) = T_rat (M' + i + 1),
          -- we have tailSum c (N' + i + 1) = tailSum c (M' + i + 1).
          -- Both are tail sums of the SAME sequence c at different positions.

          -- Define a = N' + i + 1 and b = M' + i + 1 with a < b.
          -- We have tailSum c a = tailSum c b.

          -- Claim: c_a = c_b.
          -- Proof: If c_a ≠ c_b, WLOG c_a = 0 and c_b = 1.
          --   Then tailSum c a = (1/2) * tailSum c (a+1) (since c_a = 0).
          --   And tailSum c b = 1 + (1/2) * tailSum c (b+1) (since c_b = 1).
          --   For these to be equal:
          --     (1/2) * tailSum c (a+1) = 1 + (1/2) * tailSum c (b+1)
          --     tailSum c (a+1) = 2 + tailSum c (b+1)
          --   But tailSum c (a+1) ≤ 2 and tailSum c (b+1) ≥ 0.
          --   So tailSum c (a+1) = 2 and tailSum c (b+1) = 0.
          --   tailSum c (a+1) = 2 means c_{a+1+j} = 1 for all j ≥ 0.
          --   tailSum c (b+1) = 0 means c_{b+1+j} = 0 for all j ≥ 0.
          --   So starting from a+1, all c's are 1.
          --   And starting from b+1, all c's are 0.
          --   But b+1 > a+1 (since b > a), so c_{b+1} should be 1 (from the "all 1s" pattern).
          --   But we said c_{b+1} = 0. Contradiction!
          -- So c_a = c_b.

          let a := N' + i + 1
          let b := M' + i + 1
          have hab : a < b := by omega
          have hT_ab : T_rat a = T_rat b := by
            have h1 : T_rat (N' + i + 1) = 2 * (T_rat (N' + i) - c_rat (N' + i)) := by
              have := hT_rat_succ (N' + i); convert this using 2
            have h2 : T_rat (M' + i + 1) = 2 * (T_rat (M' + i) - c_rat (M' + i)) := by
              have := hT_rat_succ (M' + i); convert this using 2
            simp only [a, b]
            rw [h1, h2, hT_ih, hc_ih]

          -- Prove c a = c b
          have hc_eq : c a = c b := by
            by_contra hne
            have hca_ne_cb : c a ≠ c b := hne
            -- WLOG c a = 0 and c b = 1 (the other case is symmetric)
            rcases hc a with hca0 | hca1 <;> rcases hc b with hcb0 | hcb1
            · -- c a = 0 and c b = 0
              exact hca_ne_cb (hca0.trans hcb0.symm)
            · -- c a = 0 and c b = 1
              -- tailSum c a = 0 + (1/2) * tailSum c (a+1)
              -- tailSum c b = 1 + (1/2) * tailSum c (b+1)
              -- These are equal, so:
              -- (1/2) * tailSum c (a+1) = 1 + (1/2) * tailSum c (b+1)
              -- tailSum c (a+1) = 2 + tailSum c (b+1)
              have hrec_a_raw : tailSum c a = c a + (1/2) * tailSum c (a + 1) := tailSum_recurrence c hc a
              have hrec_b_raw : tailSum c b = c b + (1/2) * tailSum c (b + 1) := tailSum_recurrence c hc b
              have hrec_a : tailSum c a = (1/2) * tailSum c (a + 1) := by rw [hrec_a_raw, hca0]; ring
              have hrec_b : tailSum c b = 1 + (1/2) * tailSum c (b + 1) := by rw [hrec_b_raw, hcb1]
              have hT_eq_real : tailSum c a = tailSum c b := by
                rw [← hT_rat_eq_tailSum a, ← hT_rat_eq_tailSum b]
                simp only [a, b] at hT_ab ⊢
                exact congrArg Rat.cast hT_ab
              have h1 : (1/2 : ℝ) * tailSum c (a + 1) = 1 + (1/2) * tailSum c (b + 1) := by
                rw [← hrec_a, ← hrec_b, hT_eq_real]
              have h2 : tailSum c (a + 1) = 2 + tailSum c (b + 1) := by linarith
              have hT_a1_le : tailSum c (a + 1) ≤ 2 := tailSum_le_two c hc (a + 1)
              have hT_b1_ge : tailSum c (b + 1) ≥ 0 := tailSum_nonneg c hc (b + 1)
              have hT_a1_eq_2 : tailSum c (a + 1) = 2 := by linarith
              have hT_b1_eq_0 : tailSum c (b + 1) = 0 := by linarith
              -- tailSum c (a+1) = 2 means all c_{a+1+j} = 1
              -- tailSum c (b+1) = 0 means all c_{b+1+j} = 0
              -- But b+1 > a+1, so c_{b+1} should be 1, contradiction with c_{b+1} = 0.
              have hall_ones : ∀ j, c (a + 1 + j) = 1 := by
                intro j
                by_contra hne_1
                rcases hc (a + 1 + j) with h0 | h1
                · -- c (a + 1 + j) = 0, but tailSum c (a + 1) = 2
                  -- If any coefficient is 0, the sum is strictly less than 2
                  have hsum_lt : tailSum c (a + 1) < 2 := by
                    unfold tailSum
                    have hsplit := Summable.sum_add_tsum_nat_add (j + 1) (tailSum_summable c hc (a + 1))
                    have hfinsum : ∀ k ∈ Finset.range (j + 1), c (a + 1 + k) * (1/2 : ℝ)^k ≤ (1 : ℝ) * (1/2 : ℝ)^k := by
                      intro k _; rcases hc (a + 1 + k) with hk | hk <;> simp [hk]
                    have hfinsum_strict : ∑ k ∈ Finset.range (j + 1), c (a + 1 + k) * (1/2 : ℝ)^k <
                                          ∑ k ∈ Finset.range (j + 1), (1 : ℝ) * (1/2 : ℝ)^k := by
                      apply Finset.sum_lt_sum hfinsum
                      use j; constructor
                      · simp only [Finset.mem_range]; omega
                      · simp only [h0, zero_mul, one_mul]; exact pow_pos (by norm_num : (0 : ℝ) < 1/2) j
                    have htail_after : ∀ k, c (a + 1 + (k + (j + 1))) * (1/2 : ℝ)^(k + (j + 1)) ≤
                                       (1 : ℝ) * (1/2 : ℝ)^(k + (j + 1)) := by
                      intro k
                      have hck := hc (a + 1 + (k + (j + 1)))
                      cases hck with
                      | inl h => simp [h]
                      | inr h => simp [h]
                    have htail_le : ∑' (k : ℕ), c (a + 1 + (k + (j + 1))) * (1/2 : ℝ)^(k + (j + 1)) ≤
                                    ∑' (k : ℕ), (1 : ℝ) * (1/2 : ℝ)^(k + (j + 1)) := by
                      -- Step 1: Summability of LHS
                      have hf_sum : Summable (fun k => c (a + 1 + (k + (j + 1))) * (1/2 : ℝ)^(k + (j + 1))) := by
                        have h_sum_tail := tailSum_summable c hc (a + 1)
                        exact h_sum_tail.comp_injective (add_left_injective (j + 1))
                      -- Step 2: Summability of RHS
                      have hg_sum : Summable (fun k => (1 : ℝ) * (1/2 : ℝ)^(k + (j + 1))) := by
                        have h_geom : Summable (fun k => (1/2 : ℝ)^k) :=
                          summable_geometric_of_lt_one (by norm_num) (by norm_num)
                        simp only [one_mul]
                        exact h_geom.comp_injective (add_left_injective (j + 1))
                      -- Step 3: Apply Summable.tsum_le_tsum
                      exact hf_sum.tsum_le_tsum htail_after hg_sum
                    have hgeom_full : ∑' (k : ℕ), (1/2 : ℝ)^k = 2 := by
                      rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
                    have hgeom_split := Summable.sum_add_tsum_nat_add (j + 1)
                      (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1))
                    calc ∑' k, c (a + 1 + k) * (1/2 : ℝ)^k
                        = ∑ k ∈ Finset.range (j + 1), c (a + 1 + k) * (1/2 : ℝ)^k +
                          ∑' (k : ℕ), c (a + 1 + (k + (j + 1))) * (1/2 : ℝ)^(k + (j + 1)) := hsplit.symm
                      _ < ∑ k ∈ Finset.range (j + 1), (1 : ℝ) * (1/2 : ℝ)^k +
                          ∑' (k : ℕ), c (a + 1 + (k + (j + 1))) * (1/2 : ℝ)^(k + (j + 1)) := by
                            linarith [hfinsum_strict]
                      _ ≤ ∑ k ∈ Finset.range (j + 1), (1 : ℝ) * (1/2 : ℝ)^k +
                          ∑' (k : ℕ), (1 : ℝ) * (1/2 : ℝ)^(k + (j + 1)) := by linarith [htail_le]
                      _ = 2 := by simp only [one_mul]; linarith [hgeom_split, hgeom_full]
                  linarith
                · exact hne_1 h1
              have hb1_is_1 : c (b + 1) = 1 := by
                have hb1_ge_a1 : b + 1 > a + 1 := by omega
                have hb1_eq : b + 1 = a + 1 + (b - a) := by omega
                rw [hb1_eq]
                exact hall_ones (b - a)
              -- But tailSum c (b+1) = 0 means c_{b+1} = 0 (coefficient of (1/2)^0 = 1)
              have hc_b1_zero : c (b + 1) = 0 := by
                by_contra hne
                rcases hc (b + 1) with h0 | h1
                · exact hne h0
                · -- c (b + 1) = 1, but tailSum c (b + 1) = 0
                  -- tailSum c (b + 1) = c (b + 1) + (1/2) * tailSum c (b + 2) = 1 + ... ≥ 1 > 0
                  have hrec_b1 : tailSum c (b + 1) = c (b + 1) + (1/2) * tailSum c (b + 2) :=
                    tailSum_recurrence c hc (b + 1)
                  rw [h1] at hrec_b1
                  have hT_b2_ge : tailSum c (b + 2) ≥ 0 := tailSum_nonneg c hc (b + 2)
                  linarith
              rw [hb1_is_1] at hc_b1_zero
              exact one_ne_zero hc_b1_zero
            · -- c a = 1 and c b = 0 (symmetric case)
              have hrec_a_raw : tailSum c a = c a + (1/2) * tailSum c (a + 1) := tailSum_recurrence c hc a
              have hrec_b_raw : tailSum c b = c b + (1/2) * tailSum c (b + 1) := tailSum_recurrence c hc b
              have hrec_a : tailSum c a = 1 + (1/2) * tailSum c (a + 1) := by rw [hrec_a_raw, hca1]
              have hrec_b : tailSum c b = (1/2) * tailSum c (b + 1) := by rw [hrec_b_raw, hcb0]; ring
              have hT_eq_real : tailSum c a = tailSum c b := by
                rw [← hT_rat_eq_tailSum a, ← hT_rat_eq_tailSum b]
                simp only [a, b] at hT_ab ⊢
                exact congrArg Rat.cast hT_ab
              have h1 : 1 + (1/2 : ℝ) * tailSum c (a + 1) = (1/2) * tailSum c (b + 1) := by
                rw [← hrec_a, ← hrec_b, hT_eq_real]
              have h2 : tailSum c (b + 1) = 2 + tailSum c (a + 1) := by linarith
              have hT_b1_le : tailSum c (b + 1) ≤ 2 := tailSum_le_two c hc (b + 1)
              have hT_a1_ge : tailSum c (a + 1) ≥ 0 := tailSum_nonneg c hc (a + 1)
              have hT_b1_eq_2 : tailSum c (b + 1) = 2 := by linarith
              have hT_a1_eq_0 : tailSum c (a + 1) = 0 := by linarith
              -- Now c_{b+1+j} = 1 for all j, and c_{a+1+j} = 0 for all j.
              -- But a+1 < b+1, so for j = b - a, c_{a+1+j} = c_{b+1} should be 1, contradiction.
              have hall_ones_b : ∀ j, c (b + 1 + j) = 1 := by
                intro j
                by_contra hne_1
                rcases hc (b + 1 + j) with h0 | h1
                · have hsum_lt : tailSum c (b + 1) < 2 := by
                    unfold tailSum
                    have hsplit := Summable.sum_add_tsum_nat_add (j + 1) (tailSum_summable c hc (b + 1))
                    have hfinsum_strict : ∑ k ∈ Finset.range (j + 1), c (b + 1 + k) * (1/2 : ℝ)^k <
                                          ∑ k ∈ Finset.range (j + 1), (1 : ℝ) * (1/2 : ℝ)^k := by
                      apply Finset.sum_lt_sum
                      · intro k _
                        have hck := hc (b + 1 + k)
                        cases hck with
                        | inl h => simp [h]
                        | inr h => simp [h]
                      · use j
                        constructor
                        · simp only [Finset.mem_range]; omega
                        · simp only [h0, zero_mul, one_mul]
                          exact pow_pos (by norm_num : (0 : ℝ) < 1/2) j
                    have htail_bound : ∀ k, c (b + 1 + (k + (j + 1))) * (1/2 : ℝ)^(k + (j + 1)) ≤
                                       (1 : ℝ) * (1/2 : ℝ)^(k + (j + 1)) := by
                      intro k
                      have hck := hc (b + 1 + (k + (j + 1)))
                      cases hck with
                      | inl h => simp [h]
                      | inr h => simp [h]
                    have htail_after_le : ∑' (k : ℕ), c (b + 1 + (k + (j + 1))) * (1/2 : ℝ)^(k + (j + 1)) ≤
                                       ∑' (k : ℕ), (1 : ℝ) * (1/2 : ℝ)^(k + (j + 1)) := by
                      -- Step 1: Summability of LHS
                      have hf_sum : Summable (fun k => c (b + 1 + (k + (j + 1))) * (1/2 : ℝ)^(k + (j + 1))) := by
                        have h_sum_tail := tailSum_summable c hc (b + 1)
                        exact h_sum_tail.comp_injective (add_left_injective (j + 1))
                      -- Step 2: Summability of RHS
                      have hg_sum : Summable (fun k => (1 : ℝ) * (1/2 : ℝ)^(k + (j + 1))) := by
                        have h_geom : Summable (fun k => (1/2 : ℝ)^k) :=
                          summable_geometric_of_lt_one (by norm_num) (by norm_num)
                        simp only [one_mul]
                        exact h_geom.comp_injective (add_left_injective (j + 1))
                      -- Step 3: Apply Summable.tsum_le_tsum
                      exact hf_sum.tsum_le_tsum htail_bound hg_sum
                    have hgeom_split := Summable.sum_add_tsum_nat_add (j + 1)
                      (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1))
                    have hgeom_full : ∑' (k : ℕ), (1/2 : ℝ)^k = 2 := by
                      rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
                    calc ∑' k, c (b + 1 + k) * (1/2 : ℝ)^k
                        = ∑ k ∈ Finset.range (j + 1), c (b + 1 + k) * (1/2 : ℝ)^k +
                          ∑' (k : ℕ), c (b + 1 + (k + (j + 1))) * (1/2 : ℝ)^(k + (j + 1)) := hsplit.symm
                      _ < ∑ k ∈ Finset.range (j + 1), (1 : ℝ) * (1/2 : ℝ)^k +
                          ∑' (k : ℕ), (1 : ℝ) * (1/2 : ℝ)^(k + (j + 1)) := by
                            apply add_lt_add_of_lt_of_le hfinsum_strict htail_after_le
                      _ = 2 := by simp only [one_mul]; linarith [hgeom_split, hgeom_full]
                  linarith
                · exact hne_1 h1
              -- c_{a+1+j} = 0 for all j (from tailSum c (a+1) = 0)
              have hall_zeros_a : ∀ j, c (a + 1 + j) = 0 := by
                intro j
                by_contra hne_0
                rcases hc (a + 1 + j) with h0 | h1
                · exact hne_0 h0
                · -- c (a + 1 + j) = 1, but tailSum c (a + 1) = 0, contradiction
                  have hsum_gt : tailSum c (a + 1) > 0 := by
                    unfold tailSum
                    have hsplit := Summable.sum_add_tsum_nat_add (j + 1) (tailSum_summable c hc (a + 1))
                    have hterm_pos : c (a + 1 + j) * (1/2 : ℝ)^j > 0 := by
                      rw [h1]; simp
                    have hfinsum_pos : ∑ k ∈ Finset.range (j + 1), c (a + 1 + k) * (1/2 : ℝ)^k > 0 := by
                      apply Finset.sum_pos'
                      · intro k _
                        have hck := hc (a + 1 + k)
                        cases hck with
                        | inl h => simp [h]
                        | inr h => simp [h]
                      · use j
                        constructor
                        · simp only [Finset.mem_range]; omega
                        · exact hterm_pos
                    have htail_nonneg : ∑' (k : ℕ), c (a + 1 + (k + (j + 1))) * (1/2 : ℝ)^(k + (j + 1)) ≥ 0 := by
                      apply tsum_nonneg; intro k
                      have hck := hc (a + 1 + (k + (j + 1)))
                      cases hck with
                      | inl h => simp [h]
                      | inr h => simp [h]
                    linarith [hsplit]
                  linarith
              -- Now b + 1 = a + 1 + (b - a), so c (b + 1) = c (a + 1 + (b - a)) = 0.
              -- But hall_ones_b says c (b + 1 + 0) = c (b + 1) = 1. Contradiction!
              have hb1_zero : c (b + 1) = 0 := by
                have heq : b + 1 = a + 1 + (b - a) := by omega
                rw [heq]
                exact hall_zeros_a (b - a)
              have hb1_one : c (b + 1) = 1 := hall_ones_b 0
              rw [hb1_zero] at hb1_one
              exact zero_ne_one hb1_one
            · -- c a = 1 and c b = 1
              exact hca_ne_cb (hca1.trans hcb1.symm)

          -- Now convert c a = c b to c_rat a = c_rat b
          -- Goal: c_rat (N' + (i + 1)) = c_rat (M' + (i + 1))
          -- Note: a = N' + i + 1 = N' + (i + 1) and b = M' + i + 1 = M' + (i + 1)
          -- We have hc_eq : c a = c b, i.e., c (N' + i + 1) = c (M' + i + 1)
          have ha_eq : N' + (i + 1) = a := by omega
          have hb_eq : M' + (i + 1) = b := by omega
          simp only [c_rat, ha_eq, hb_eq, hc_eq]

    -- Step 11.2: From hinduction k, we get c_rat (N' + k) = c_rat (M' + k)
    -- We need to prove c (N' + k) = c (M' + k)
    have hc_rat_eq := (hinduction k).2
    -- c_rat n = 1 if c n = 1 else 0
    -- So c_rat (N' + k) = c_rat (M' + k) implies c (N' + k) = c (M' + k)
    rcases hc (N' + k) with hN | hN <;> rcases hc (M' + k) with hM | hM
    · exact hN.trans hM.symm
    · -- c (N' + k) = 0 and c (M' + k) = 1
      -- c_rat (N' + k) = if c (N' + k) = 1 then 1 else 0 = 0 (since c (N' + k) = 0 ≠ 1)
      -- c_rat (M' + k) = if c (M' + k) = 1 then 1 else 0 = 1 (since c (M' + k) = 1)
      -- So hc_rat_eq : 0 = 1, contradiction
      have h1 : c_rat (N' + k) = 0 := by
        simp only [c_rat]
        have hne : c (N' + k) ≠ 1 := by rw [hN]; exact zero_ne_one
        simp only [if_neg hne]
      have h2 : c_rat (M' + k) = 1 := by
        simp only [c_rat]
        have heq : c (M' + k) = 1 := hM
        simp only [if_pos heq]
      rw [h1, h2] at hc_rat_eq
      exact False.elim (zero_ne_one hc_rat_eq)
    · -- c (N' + k) = 1 and c (M' + k) = 0
      -- c_rat (N' + k) = 1, c_rat (M' + k) = 0, so hc_rat_eq : 1 = 0, contradiction
      have h1 : c_rat (N' + k) = 1 := by
        simp only [c_rat]
        have heq : c (N' + k) = 1 := hN
        simp only [if_pos heq]
      have h2 : c_rat (M' + k) = 0 := by
        simp only [c_rat]
        have hne : c (M' + k) ≠ 1 := by rw [hM]; exact zero_ne_one
        simp only [if_neg hne]
      rw [h1, h2] at hc_rat_eq
      exact False.elim (one_ne_zero hc_rat_eq)
    · exact hN.trans hM.symm

  -- Step 12: Define periodicity parameters
  let period := M' - N'
  have hperiod_pos : period ≥ 1 := by omega

  -- Step 12.1: Restate periodicity in the required form
  have hper_form : ∀ k, c (N' + period + k) = c (N' + k) := by
    intro k
    have h1 : N' + period + k = M' + k := by simp only [period]; omega
    rw [h1]
    exact (hperiod k).symm

  -- Step 13: Conclude IsEventuallyPeriodic
  unfold IsEventuallyPeriodic
  exact ⟨N', period, hperiod_pos, hper_form⟩

/-- KEY LEMMA 2: If c is eventually periodic, then f(2/3) has odd denominator.

    Proof sketch:
    - With period m starting at N, write:
      f(x) = Σ_{i < N} c_i x^i + x^N * (Σ_{j < m} c_{N+j} x^j) / (1 - x^m)
    - At x = 2/3:
      * The finite sum has denominator dividing 3^{N-1} (odd)
      * 1/(1-(2/3)^m) = 3^m/(3^m - 2^m) where 3^m - 2^m is odd
      * All denominators are products of odd numbers, hence odd
    - Therefore f(2/3) = (integer)/(odd integer) after simplification
    - But 3/2 has even denominator 2, contradiction!
-/
lemma eventually_periodic_implies_odd_denom (c : ℕ → ℝ) (hc : ∀ n, c n = 0 ∨ c n = 1)
    (N m : ℕ) (hm : m ≥ 1) (hper : ∀ k, c (N + m + k) = c (N + k))
    (hf23 : ∑' (i : ℕ), c i * (2/3 : ℝ)^i = 3/2) : False := by
  /-
    PROOF STRUCTURE (Closed form gives odd denominator, contradicting 3/2)

    Step 1: Define rational coefficients c_rat where c_rat i = 1 if c i = 1 else 0
    Step 2: Define finite sum finSum = Σ_{i < N} c_rat i * (2/3)^i
    Step 3: Define period sum perSum = Σ_{j < m} c_rat (N+j) * (2/3)^j
    Step 4: Define closed form q = finSum + (2/3)^N * perSum / (1 - (2/3)^m)
    Step 5: Show q.den is odd using:
      5.1: finSum has odd denominator (by sum_01_two_thirds_odd_denom)
      5.2: perSum has odd denominator
      5.3: (2/3)^N has odd denominator (by two_thirds_pow_odd_denom)
      5.4: (1-(2/3)^m)⁻¹ has odd denominator (since num divides 3^m-2^m which is odd)
      5.5: Product of rationals with odd denominators has odd denominator
    Step 6: Since q.den is odd, q ≠ 3/2 (by rat_with_odd_denom_ne_three_halves)
    Step 7: Show (q : ℝ) = tsum (the closed form equals the infinite sum)
    Step 8: From hf23, (q : ℝ) = 3/2, so q = 3/2 by Rat.cast_injective
    Step 9: Contradiction: q ≠ 3/2 but q = 3/2
  -/

  -- Step 1: Define the rational coefficients
  let c_rat : ℕ → ℚ := fun i => if c i = 1 then 1 else 0

  -- Step 1.1: c_rat takes values in {0, 1}
  have hc_rat_01 : ∀ i, c_rat i = 0 ∨ c_rat i = 1 := fun i => by
    simp only [c_rat]
    by_cases h : c i = 1 <;> simp [h]

  -- Step 1.2: c_rat cast to ℝ equals c
  have hc_rat_cast : ∀ i, (c_rat i : ℝ) = c i := fun i => by
    simp only [c_rat]
    rcases hc i with hi | hi <;> simp [hi]

  -- Step 2: Define the finite sum (first N terms)
  let finSum : ℚ := ∑ i ∈ Finset.range N, c_rat i * (2/3 : ℚ)^i

  -- Step 3: Define the period sum (one period of m terms)
  let perSum : ℚ := ∑ j ∈ Finset.range m, c_rat (N + j) * (2/3 : ℚ)^j

  -- Step 4: The denominator 1 - (2/3)^m is nonzero
  have h_denom_ne : (1 - (2/3 : ℚ)^m) ≠ 0 := by
    have h1 : (2/3 : ℚ)^m < 1 := by
      have : (2/3 : ℚ) < 1 := by norm_num
      exact pow_lt_one₀ (by norm_num) this (Nat.one_le_iff_ne_zero.mp hm)
    linarith

  -- Step 4.1: Define the closed form rational
  let q : ℚ := finSum + (2/3 : ℚ)^N * perSum / (1 - (2/3 : ℚ)^m)

  -- Step 5: Show q.den is odd
  -- The proof shows:
  --   5.1: finSum has odd denominator (sum of {0,1}*(2/3)^i with odd-denom terms)
  --   5.2: perSum has odd denominator (similar reasoning)
  --   5.3: (2/3)^N has odd denominator (3^N is odd)
  --   5.4: (1-(2/3)^m)⁻¹ has odd denominator (numerator divides 3^m-2^m which is odd)
  --   5.5: The combination q = finSum + (2/3)^N * perSum / (1-(2/3)^m) has odd denominator
  --        because products and sums of rationals with odd denominators have odd denominators
  have hq_odd : Odd q.den := by
    -- Step 5.1: finSum has odd denominator
    have h_fin_odd : Odd finSum.den := sum_01_two_thirds_odd_denom c_rat hc_rat_01 N
    -- Step 5.2: perSum has odd denominator
    have h_per_odd : Odd perSum.den :=
      sum_01_two_thirds_odd_denom (fun j => c_rat (N + j)) (fun j => hc_rat_01 (N + j)) m
    -- Step 5.3: (2/3)^N has odd denominator
    have h_pow_odd : Odd ((2/3 : ℚ)^N).den := two_thirds_pow_odd_denom N
    -- Step 5.4: (1-(2/3)^m)⁻¹ has odd denominator
    have h_inv_odd : Odd ((1 - (2/3 : ℚ)^m)⁻¹).den := inv_one_sub_two_thirds_pow_odd_denom m hm

    -- Step 5.5: The tail term (2/3)^N * perSum / (1-(2/3)^m) has odd denominator
    let tail : ℚ := (2/3 : ℚ)^N * perSum / (1 - (2/3 : ℚ)^m)

    have h_tail_odd : Odd tail.den := by
      simp only [tail, div_eq_mul_inv]
      have h_prod_dvd : ((2/3 : ℚ)^N * perSum * (1 - (2/3 : ℚ)^m)⁻¹).den ∣
                        ((2/3 : ℚ)^N).den * perSum.den * ((1 - (2/3 : ℚ)^m)⁻¹).den :=
        mul_mul_den_dvd ((2/3 : ℚ)^N) perSum ((1 - (2/3 : ℚ)^m)⁻¹)
      have h_big_odd : Odd (((2/3 : ℚ)^N).den * perSum.den * ((1 - (2/3 : ℚ)^m)⁻¹).den) :=
        (h_pow_odd.mul h_per_odd).mul h_inv_odd
      exact Odd.of_dvd_nat h_big_odd h_prod_dvd

    -- Step 5.6: q = finSum + tail has odd denominator
    have h_sum_dvd : q.den ∣ finSum.den * tail.den := Rat.add_den_dvd finSum tail
    have h_prod_odd : Odd (finSum.den * tail.den) := h_fin_odd.mul h_tail_odd
    exact Odd.of_dvd_nat h_prod_odd h_sum_dvd

  -- Step 6: q ≠ 3/2 (since q has odd denominator)
  have hq_ne : q ≠ 3/2 := odd_denom_ne_three_halves q hq_odd

  -- Step 7: Show (q : ℝ) = ∑' i, c i * (2/3)^i
  -- This requires showing the closed form equals the infinite sum
  have hq_eq_tsum : (q : ℝ) = ∑' i, c i * (2/3 : ℝ)^i := by
    have h_summable := series_summable_at_two_thirds c hc

    -- Step 7.1: Split the infinite sum at position N
    have h_split_raw := Summable.sum_add_tsum_nat_add N h_summable

    have h_tsum_reindex : ∑' (i : ℕ), c (i + N) * (2/3 : ℝ)^(i + N) =
                          ∑' (i : ℕ), c (N + i) * (2/3 : ℝ)^(N + i) := by
      apply tsum_congr
      intro i
      ring_nf

    have h_split : ∑' i, c i * (2/3 : ℝ)^i =
                   ∑ i ∈ Finset.range N, c i * (2/3 : ℝ)^i +
                   ∑' i, c (N + i) * (2/3 : ℝ)^(N + i) := by
      rw [← h_split_raw, h_tsum_reindex]

    -- Step 7.2: Factor out (2/3)^N from the tail
    have h_tail_factor : ∑' i, c (N + i) * (2/3 : ℝ)^(N + i) =
                         (2/3 : ℝ)^N * ∑' i, c (N + i) * (2/3 : ℝ)^i := by
      rw [← tsum_mul_left]
      apply tsum_congr; intro i; rw [pow_add]; ring

    -- Step 7.3: Show the tail series is summable
    have h_xm_lt_1 : (2/3 : ℝ)^m < 1 := by
      have h1 : (2/3 : ℝ) < 1 := by norm_num
      exact pow_lt_one₀ (by norm_num) h1 (Nat.one_le_iff_ne_zero.mp hm)
    have h_denom_ne_real : 1 - (2/3 : ℝ)^m ≠ 0 := by linarith

    have h_tail_summable : Summable (fun i => c (N + i) * (2/3 : ℝ)^i) := by
      have h2 : Summable (fun n => c (n + N) * (2/3 : ℝ)^(n + N)) :=
        (summable_nat_add_iff N).mpr h_summable
      have h3 : Summable (fun n => c (N + n) * (2/3 : ℝ)^(N + n)) := by
        have heq : (fun n => c (N + n) * (2/3 : ℝ)^(N + n)) =
                   (fun n => c (n + N) * (2/3 : ℝ)^(n + N)) := by
          funext n; ring_nf
        rw [heq]; exact h2
      have h4 : (fun n => c (N + n) * (2/3 : ℝ)^(N + n)) =
                (fun n => (2/3 : ℝ)^N * (c (N + n) * (2/3 : ℝ)^n)) := by
        funext n; rw [pow_add]; ring
      rw [h4] at h3
      have h5 : (2/3 : ℝ)^N ≠ 0 := pow_ne_zero N (by norm_num)
      exact (summable_mul_left_iff h5).mp h3

    -- Step 7.4: The periodic series has closed form F/(1-(2/3)^m)
    have h_tail_geometric : ∑' i, c (N + i) * (2/3 : ℝ)^i =
                            (∑ j ∈ Finset.range m, c (N + j) * (2/3 : ℝ)^j) / (1 - (2/3 : ℝ)^m) := by
      have h_split_m_raw := Summable.sum_add_tsum_nat_add m h_tail_summable

      have h_tsum_reindex_m : ∑' (i : ℕ), c (N + (i + m)) * (2/3 : ℝ)^(i + m) =
                              ∑' (j : ℕ), c (N + m + j) * (2/3 : ℝ)^(m + j) := by
        apply tsum_congr
        intro j
        ring_nf

      have h_split_m : ∑' i, c (N + i) * (2/3 : ℝ)^i =
                       ∑ i ∈ Finset.range m, c (N + i) * (2/3 : ℝ)^i +
                       ∑' j, c (N + m + j) * (2/3 : ℝ)^(m + j) := by
        rw [← h_split_m_raw, h_tsum_reindex_m]

      have h_tail_per : ∑' j, c (N + m + j) * (2/3 : ℝ)^(m + j) =
                        ∑' j, c (N + j) * (2/3 : ℝ)^(m + j) := by
        apply tsum_congr; intro j; rw [hper j]

      have h_tail_fact : ∑' j, c (N + j) * (2/3 : ℝ)^(m + j) =
                         (2/3 : ℝ)^m * ∑' j, c (N + j) * (2/3 : ℝ)^j := by
        rw [← tsum_mul_left]; apply tsum_congr; intro j; rw [pow_add]; ring

      let F : ℝ := ∑ i ∈ Finset.range m, c (N + i) * (2/3 : ℝ)^i
      let S : ℝ := ∑' i, c (N + i) * (2/3 : ℝ)^i

      have h_eq : S = F + (2/3 : ℝ)^m * S := by
        calc S = ∑' i, c (N + i) * (2/3 : ℝ)^i := rfl
          _ = ∑ i ∈ Finset.range m, c (N + i) * (2/3 : ℝ)^i +
              ∑' j, c (N + m + j) * (2/3 : ℝ)^(m + j) := h_split_m
          _ = F + ∑' j, c (N + m + j) * (2/3 : ℝ)^(m + j) := rfl
          _ = F + ∑' j, c (N + j) * (2/3 : ℝ)^(m + j) := by rw [h_tail_per]
          _ = F + (2/3 : ℝ)^m * S := by rw [h_tail_fact]

      have h_final : S = F / (1 - (2/3 : ℝ)^m) := by
        field_simp [h_denom_ne_real]; linarith [h_eq]
      exact h_final

    -- Step 7.5: Convert rational sums to real sums
    have h_fin_cast : (finSum : ℝ) = ∑ i ∈ Finset.range N, c i * (2/3 : ℝ)^i := by
      simp only [finSum, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat]
      apply Finset.sum_congr rfl; intro i _; rw [hc_rat_cast i]

    have h_per_cast : (perSum : ℝ) = ∑ j ∈ Finset.range m, c (N + j) * (2/3 : ℝ)^j := by
      simp only [perSum, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat]
      apply Finset.sum_congr rfl; intro j _; rw [hc_rat_cast (N + j)]

    have h_pow_cast_N : (((2/3 : ℚ)^N) : ℝ) = (2/3 : ℝ)^N := by
      simp only [Rat.cast_div, Rat.cast_ofNat]

    have h_denom_cast : (((1 - (2/3 : ℚ)^m)) : ℝ) = 1 - (2/3 : ℝ)^m := by
      simp only [Rat.cast_div, Rat.cast_ofNat]

    -- Step 7.6: Put it together using a direct equality chain
    have h_q_real : (q : ℝ) = (finSum : ℝ) + (((2/3 : ℚ)^N) : ℝ) * (perSum : ℝ) / (((1 - (2/3 : ℚ)^m)) : ℝ) := by
      simp only [q, Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_sub, Rat.cast_one, Rat.cast_ofNat]

    rw [h_q_real, h_fin_cast, h_per_cast, h_pow_cast_N, h_denom_cast]

    -- Rewrite: (a * b) / c = a * (b / c)
    have h_rearrange : ((2/3 : ℝ)^N * ∑ j ∈ Finset.range m, c (N + j) * (2/3 : ℝ)^j) / (1 - (2/3 : ℝ)^m) =
                       (2/3 : ℝ)^N * ((∑ j ∈ Finset.range m, c (N + j) * (2/3 : ℝ)^j) / (1 - (2/3 : ℝ)^m)) := by
      rw [mul_div_assoc]

    rw [h_rearrange, ← h_tail_geometric]

    -- Now the goal is: ∑ + (2/3)^N * (∑' c(N+i)*(2/3)^i) = ∑' c_i*(2/3)^i
    rw [← h_tail_factor]

    -- Now goal is: ∑ + ∑' c(N+i)*(2/3)^(N+i) = ∑' c_i*(2/3)^i
    rw [← h_split]

  -- Step 8: Derive contradiction
  -- From hf23: ∑' i, c i * (2/3)^i = 3/2
  -- From hq_eq_tsum: (q : ℝ) = ∑' i, c i * (2/3)^i
  -- So (q : ℝ) = 3/2
  have hq_eq_32_real : (q : ℝ) = (3/2 : ℝ) := by rw [hq_eq_tsum, hf23]

  -- Step 8.1: Convert to rational equality using injectivity
  have h32_cast : (3/2 : ℝ) = ((3/2 : ℚ) : ℝ) := by simp only [Rat.cast_div, Rat.cast_ofNat]
  rw [h32_cast] at hq_eq_32_real
  have hq_eq_32 : q = (3/2 : ℚ) := Rat.cast_injective hq_eq_32_real

  -- Step 9: Contradiction
  exact hq_ne hq_eq_32

-- ============================================================================
-- Main Theorem
-- ============================================================================

theorem Putnam_exercise_2017_b3 (f : ℝ → ℝ) (c : ℕ → ℝ)
  (hf : f = λ x => (∑' (i : ℕ), (c i) * x^i))
  (hc : ∀ n, c n = 0 ∨ c n = 1)
  (hf1 : f (2/3) = 3/2) :
  Irrational (f (1/2)) := by
  -- Step 1: Unfold the definition of Irrational
  -- Irrational x means x ∉ range (Rat.cast : ℚ → ℝ)
  rw [Irrational, Set.mem_range]
  push_neg
  intro q hq

  -- Step 2: Express q as p/d where d > 0
  -- Every rational q can be written as q.num / q.den
  obtain ⟨p, d, hd_pos, hpd⟩ : ∃ p : ℤ, ∃ d : ℕ, d ≥ 1 ∧ (q : ℝ) = p / d := by
    use q.num, q.den
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr q.den_ne_zero
    · simp only [Rat.cast_def]

  -- Step 3: From hq and hf, we have Σ c_i * (1/2)^i = p/d
  have hsum_half : ∑' (i : ℕ), c i * (1/2 : ℝ)^i = p / d := by
    rw [← hpd, hq]
    simp only [hf]

  -- Step 4: By KEY LEMMA 1, c is eventually periodic
  have hep : IsEventuallyPeriodic c :=
    rational_implies_eventually_periodic c hc p d hd_pos hsum_half

  -- Step 5: Extract the periodicity parameters N and m
  obtain ⟨N, m, hm, hper⟩ := hep

  -- Step 6: Establish that f(2/3) = 3/2 as a tsum
  have hsum_23 : ∑' (i : ℕ), c i * (2/3 : ℝ)^i = 3/2 := by
    have h1 : f (2/3) = ∑' (i : ℕ), c i * (2/3 : ℝ)^i := by simp only [hf]
    rw [← h1]
    exact hf1

  -- Step 7: Apply KEY LEMMA 2 to get contradiction
  -- An eventually periodic series at 2/3 gives odd denominator,
  -- but 3/2 has even denominator
  exact eventually_periodic_implies_odd_denom c hc N m hm hper hsum_23
