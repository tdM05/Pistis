import Mathlib

set_option maxHeartbeats 400000

noncomputable section

open scoped BigOperators
open BigOperators Finset Complex

/-Informal Statement

Let $n$ be a positive integer, and let $f_{n}(z)=n+(n-1) z+$ $(n-2) z^{2}+\cdots+z^{n-1}$. Prove that $f_{n}$ has no roots in the closed unit disk $\{z \in \mathbb{C}:|z| \leq 1\}$.
-/

/-Informal Proof

Note first that $f_n(1) > 0$, so $1$ is not a root of $f_n$.
Next, note that
\[
(z-1)f_n(z) = z^n + \cdots + z - n;
\]
however, for $\left| z \right| \leq 1$, we have 
$\left| z^n + \cdots + z \right| \leq n$ by the triangle inequality;
equality can only occur if $z,\dots,z^n$ have norm 1 and the same argument, which only happens for $z=1$.
Thus there can be no root of $f_n$ with $|z| \leq 1$.
-/

/-
  Formal Proof Strategy:
  1. f_n(1) > 0, so z = 1 is not a root
  2. Key identity: (z-1) * f_n(z) = ∑_{i=1}^{n} z^i - n = z + z² + ... + z^n - n
  3. For |z| ≤ 1, z ≠ 1: |z + z² + ... + z^n| < n by strict triangle inequality
  4. Therefore if f_n(z) = 0 and z ≠ 1, then 0 = (z-1)*f_n(z) = ∑ z^i - n
     implies |∑ z^i| = n, contradicting step 3.
-/

-- Step 1: f_n(1) ≠ 0 (the sum is positive)
-- The sum ∑_{i=0}^{n-1} (n-i) = n + (n-1) + ... + 1 = n(n+1)/2 > 0 for n > 0
lemma fn_at_one_ne_zero (n : ℕ) (hn : n > 0) :
    (∑ i : Fin n, ((n : ℂ) - ↑(i : ℕ)) * (1 : ℂ)^(i : ℕ)) ≠ 0 := by
  -- Simplify 1^i = 1 and cancel multiplication by 1
  simp only [one_pow, mul_one]
  -- Extract the real part of the complex sum
  have hreal : (∑ i : Fin n, ((n : ℂ) - ↑(i : ℕ))).re =
      ∑ i : Fin n, ((n : ℝ) - ↑(i : ℕ)) := by
    -- Use the continuous linear map property of .re
    conv_lhs => rw [← Complex.reCLM_apply]
    rw [map_sum]
    apply sum_congr rfl
    intro i _
    simp only [Complex.reCLM_apply, Complex.sub_re, Complex.natCast_re]
  -- Show the real sum is positive
  have hpos : (0 : ℝ) < ∑ i : Fin n, ((n : ℝ) - ↑(i : ℕ)) := by
    -- The sum is nonempty since n > 0
    have hnonempty : (Finset.univ : Finset (Fin n)).Nonempty := by
      rw [Finset.univ_nonempty_iff]
      exact Fin.pos_iff_nonempty.mp hn
    -- Apply sum_pos: each term is positive
    apply sum_pos
    · intro i _
      -- For i : Fin n, we have i < n, so n - i > 0
      have hi : (i : ℕ) < n := i.isLt
      simp only [sub_pos, Nat.cast_lt]
      exact hi
    · exact hnonempty
  -- Now derive contradiction: if the sum is 0, its real part must be 0
  intro hzero
  rw [hzero] at hreal
  simp only [Complex.zero_re] at hreal
  linarith

-- Step 2: Key identity (z-1)*f_n(z) = ∑_{i=0}^{n-1} z^{i+1} - n
-- This is the algebraic identity: (z-1) * ∑_{i=0}^{n-1} (n-i) * z^i = z + z² + ... + z^n - n
lemma key_identity (n : ℕ) (z : ℂ) :
    (z - 1) * (∑ i : Fin n, ((n : ℂ) - ↑(i : ℕ)) * z^(i : ℕ)) =
    (∑ i ∈ Finset.range n, z^(i + 1)) - n := by
  -- Convert Fin sum to range sum for easier manipulation
  have hconv : ∀ m : ℕ, ∑ i : Fin m, ((m : ℂ) - ↑(i : ℕ)) * z^(i : ℕ) =
      ∑ i ∈ range m, ((m : ℂ) - ↑i) * z^i := by
    intro m
    rw [← Fin.sum_univ_eq_sum_range]
  rw [hconv]

  -- Use induction on n
  induction n with
  | zero =>
    -- Base case: both sides are 0
    simp
  | succ m ih =>
    -- Inductive step: go from m to m+1

    -- Split off the last term from both sums
    rw [range_add_one, sum_insert notMem_range_self]

    -- LHS: (z-1) * ((m+1 - m) * z^m + ∑_{i=0}^{m-1} (m+1-i) * z^i)
    -- = (z-1) * z^m + (z-1) * ∑_{i=0}^{m-1} (m+1-i) * z^i
    have hcoeff : (↑(m + 1) : ℂ) - ↑m = 1 := by simp
    rw [hcoeff, one_mul]
    rw [mul_add, mul_comm (z - 1) (z^m)]

    -- Expand ∑_{i=0}^{m-1} (m+1-i)*z^i = ∑_{i=0}^{m-1} (m-i)*z^i + ∑_{i=0}^{m-1} z^i
    have hsum_split : ∑ i ∈ range m, ((↑(m + 1) : ℂ) - ↑i) * z^i =
        ∑ i ∈ range m, ((m : ℂ) - ↑i) * z^i + ∑ i ∈ range m, z^i := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro i _
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    rw [hsum_split, mul_add]

    -- Use induction hypothesis
    rw [ih]

    -- (z-1) * ∑ z^i = z^m - 1
    have hgeom : (z - 1) * ∑ i ∈ range m, z^i = z^m - 1 := by
      rw [mul_comm]
      exact geom_sum_mul z m
    rw [hgeom]

    -- z^m * (z-1) = z^{m+1} - z^m
    have hpow : z^m * (z - 1) = z^(m+1) - z^m := by ring

    rw [hpow]

    -- Now combine: z^{m+1} - z^m + (∑ z^{i+1} - m) + (z^m - 1)
    -- = z^{m+1} + ∑ z^{i+1} - m - 1
    -- = ∑_{i=0}^m z^{i+1} - (m+1)
    simp only [Nat.cast_add, Nat.cast_one]
    -- RHS: z^{m+1} + ∑_{i=0}^{m-1} z^{i+1} - (m+1)
    rw [sum_insert notMem_range_self]
    ring

-- Helper lemma: on unit circle, z.re^2 + z.im^2 = 1
lemma unit_circle_norm (z : ℂ) (hz_eq : ‖z‖ = 1) : z.re^2 + z.im^2 = 1 := by
  have hnorm : ‖z‖^2 = normSq z := Complex.sq_norm z
  rw [hz_eq] at hnorm
  simp only [one_pow] at hnorm
  -- normSq z = z.re^2 + z.im^2
  have hnormSq_def : normSq z = z.re * z.re + z.im * z.im := by
    rfl
  rw [hnormSq_def] at hnorm
  -- Convert multiplication to powers
  have h1 : z.re * z.re = z.re^2 := (sq z.re).symm
  have h2 : z.im * z.im = z.im^2 := (sq z.im).symm
  rw [h1, h2] at hnorm
  exact hnorm.symm

-- Helper: alternating sum ∑_{i=0}^{2k-1} (-1)^i = 0
lemma alternating_sum_even (k : ℕ) : ∑ i ∈ range (2 * k), (-1 : ℂ)^i = 0 := by
  induction k with
  | zero => simp
  | succ m ih =>
    have h : 2 * (m + 1) = 2 * m + 2 := by ring
    rw [h, Finset.sum_range_add]
    simp only [ih, zero_add, sum_range_succ, range_one, sum_singleton]
    ring_nf

-- Helper: alternating sum for odd n: ∑_{i=0}^{2k} (-1)^i = 1
lemma alternating_sum_odd (k : ℕ) : ∑ i ∈ range (2 * k + 1), (-1 : ℂ)^i = 1 := by
  rw [sum_range_succ]
  simp only [alternating_sum_even, zero_add]
  have h : (-1 : ℂ) ^ (2 * k) = 1 := by
    rw [pow_mul]
    simp
  rw [h]

-- Step 3: Bound on sum of powers when |z| ≤ 1 and z ≠ 1
-- |∑_{i=0}^{n-1} z^{i+1}| < n for z on or inside unit circle, z ≠ 1
-- Note: For |z| = 1 and z = -1, we need n ≥ 2. But n = 1 case is handled separately.
lemma sum_pow_norm_lt (n : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) (hn : n ≥ 2) :
    ‖∑ i ∈ Finset.range n, z^(i + 1)‖ < n := by
  by_cases hz' : ‖z‖ < 1
  · -- Case |z| < 1: strict inequality from triangle inequality
    calc ‖∑ i ∈ range n, z^(i + 1)‖
        ≤ ∑ i ∈ range n, ‖z^(i + 1)‖ := norm_sum_le _ _
      _ = ∑ i ∈ range n, ‖z‖^(i + 1) := by simp [norm_pow]
      _ ≤ ∑ i ∈ range n, ‖z‖ := by
          -- Each term |z|^{i+1} ≤ |z| since |z| < 1 and i+1 ≥ 1
          apply sum_le_sum
          intro i _
          have h1 : ‖z‖^(i + 1) ≤ ‖z‖^1 := by
            exact pow_le_pow_of_le_one (norm_nonneg z) hz'.le
              (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero i))
          simp at h1 ⊢
          exact h1
      _ = n * ‖z‖ := by simp
      _ < n * 1 := by
          -- n * |z| < n since |z| < 1 and n > 0
          have hpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega : n > 0)
          exact (mul_lt_mul_iff_right₀ hpos).mpr hz'
      _ = n := mul_one (n : ℝ)

  · -- Case |z| = 1
    push_neg at hz'
    have hz_eq : ‖z‖ = 1 := le_antisymm hz hz'
    have hz_unit : z.re^2 + z.im^2 = 1 := unit_circle_norm z hz_eq

    -- Rewrite ∑ z^{i+1} = z * ∑ z^i
    have hshift : ∑ i ∈ range n, z^(i + 1) = z * ∑ i ∈ range n, z^i := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      rw [pow_succ, mul_comm]

    -- Use geometric sum formula: ∑_{i=0}^{n-1} z^i = (z^n - 1)/(z - 1)
    have hgeom : ∑ i ∈ range n, z^i = (z^n - 1) / (z - 1) := geom_sum_eq hz1 n

    rw [hshift, hgeom]

    have h1sub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1

    calc ‖z * ((z^n - 1) / (z - 1))‖
        = ‖z‖ * ‖(z^n - 1) / (z - 1)‖ := norm_mul z _
      _ = 1 * ‖(z^n - 1) / (z - 1)‖ := by rw [hz_eq]
      _ = ‖(z^n - 1) / (z - 1)‖ := one_mul _
      _ = ‖z^n - 1‖ / ‖z - 1‖ := norm_div _ _
      _ < n := by
          -- Use |z^n - 1| = |(z-1)(z^{n-1} + ... + 1)| = |z-1| * |∑ z^i|
          have hfact : z^n - 1 = (z - 1) * (∑ i ∈ range n, z^i) := by
            have h := geom_sum_mul z n
            -- h : (∑ i ∈ range n, z^i) * (z - 1) = z^n - 1
            rw [mul_comm]
            exact h.symm
          rw [hfact, norm_mul]
          have hden_pos : 0 < ‖z - 1‖ := norm_pos_iff.mpr h1sub
          -- After simplification, we need |∑ z^i| < n
          have heq : ‖z - 1‖ * ‖∑ i ∈ range n, z ^ i‖ / ‖z - 1‖ = ‖∑ i ∈ range n, z ^ i‖ := by
            field_simp
          rw [heq]

          -- Now we need |∑_{i=0}^{n-1} z^i| < n for z on unit circle with z ≠ 1
          by_cases hzneg : z = -1
          · -- Case z = -1: alternating sum ∑ (-1)^i
            subst hzneg
            -- For n ≥ 2, the alternating sum 1 - 1 + 1 - 1 + ... is either 0 or 1
            have hbound : ‖∑ i ∈ range n, (-1 : ℂ)^i‖ ≤ 1 := by
              by_cases hn_even : Even n
              · -- n even: sum = 0
                obtain ⟨k, hk⟩ := hn_even
                have h2k : 2 * k = k + k := by ring
                rw [hk, h2k] at *
                conv_lhs => rw [show k + k = 2 * k by ring, alternating_sum_even]
                simp
              · -- n odd: sum = 1
                have hn_odd : Odd n := Nat.not_even_iff_odd.mp hn_even
                obtain ⟨k, hk⟩ := hn_odd
                rw [hk, alternating_sum_odd]
                simp
            -- Since n ≥ 2: |sum| ≤ 1 < n
            calc ‖∑ i ∈ range n, (-1 : ℂ) ^ i‖
                ≤ 1 := hbound
              _ < n := by
                  have h : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
                  exact h

          · -- Case z ≠ -1, z ≠ 1, |z| = 1
            -- Use strict triangle inequality: |1 + z| < 2 when z ≠ ±1 on unit circle

            -- First show z.re < 1 (since z ≠ 1 on unit circle)
            have hne1_re : z.re < 1 := by
              by_contra h
              push_neg at h
              have hre_eq : z.re = 1 := by
                have hre_le : z.re ≤ 1 := by
                  calc z.re ≤ |z.re| := le_abs_self _
                    _ ≤ ‖z‖ := Complex.abs_re_le_norm z
                    _ = 1 := hz_eq
                linarith
              -- If Re(z) = 1 and |z| = 1, then z = 1
              have him_eq : z.im = 0 := by
                have h1 : z.re^2 + z.im^2 = 1 := hz_unit
                rw [hre_eq] at h1
                nlinarith [sq_nonneg z.im, h1]
              have hz_eq1 : z = 1 := Complex.ext hre_eq him_eq
              exact hz1 hz_eq1

            -- Also show z.re > -1 (since z ≠ -1 on unit circle)
            have hre_gt_neg1 : z.re > -1 := by
              by_contra h
              push_neg at h
              have hre_eq : z.re = -1 := by
                have hre_ge : z.re ≥ -1 := by
                  calc z.re ≥ -|z.re| := neg_abs_le _
                    _ ≥ -‖z‖ := by linarith [Complex.abs_re_le_norm z]
                    _ = -1 := by rw [hz_eq]
                linarith
              have him_eq : z.im = 0 := by
                have h1 : z.re^2 + z.im^2 = 1 := hz_unit
                rw [hre_eq] at h1
                nlinarith [sq_nonneg z.im, h1]
              have hz_eq_neg1 : z = -1 := by
                apply Complex.ext
                · exact hre_eq
                · simp [him_eq]
              exact hzneg hz_eq_neg1

            -- Strict bound: |1 + z| < 2
            have h_one_plus_z : ‖(1:ℂ) + z‖ < 2 := by
              rw [show (1:ℂ) + z = -(((-1:ℂ)) - z) by ring]
              rw [norm_neg]
              have hnormSq_sub : ‖(-1:ℂ) - z‖^2 = normSq ((-1:ℂ) - z) := Complex.sq_norm _
              have hexpand : normSq ((-1:ℂ) - z) = (-1 - z.re)^2 + z.im^2 := by
                have hdef : normSq ((-1:ℂ) - z) = ((-1:ℂ) - z).re * ((-1:ℂ) - z).re +
                    ((-1:ℂ) - z).im * ((-1:ℂ) - z).im := rfl
                simp only [sub_re, neg_re, one_re, sub_im, neg_im, one_im] at hdef
                convert hdef using 1
                ring
              have h1 : ‖(-1:ℂ) - z‖^2 = 2 + 2*z.re := by
                rw [hnormSq_sub, hexpand]
                -- Use hz_unit : z.re^2 + z.im^2 = 1
                nlinarith [hz_unit]
              have h3 : 2 + 2*z.re < 4 := by linarith
              have h4 : ‖(-1:ℂ) - z‖^2 < 4 := by rw [h1]; exact h3
              have h5 : ‖(-1:ℂ) - z‖ < 2 := by
                have h6 : ‖(-1:ℂ) - z‖ ≥ 0 := norm_nonneg _
                nlinarith [h4, h6, sq_nonneg (‖(-1:ℂ) - z‖)]
              exact h5

            -- For n ≥ 2: |∑ z^k| ≤ |1 + z| + |z² + ... + z^{n-1}| < 2 + (n-2) = n
            -- Since n ≥ 2, we can write n = k + 2 for some k ≥ 0
            obtain ⟨k', hk'⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
            rw [hk']
            -- We need to prove |∑ z^i| < k' + 2
            -- Note: ∑ 1^i for i in Ico 2 (k'+2) has k' terms
            have hsum_bound : ∑ i ∈ Ico 2 (k' + 2), ‖z ^ i‖ = k' := by
              have hcard : (Ico 2 (k' + 2)).card = k' := by
                rw [Nat.card_Ico]
                omega
              conv_lhs =>
                apply congrArg
                ext i
                rw [norm_pow, hz_eq, one_pow]
              rw [sum_const]
              simp only [hcard, nsmul_eq_mul, mul_one]
            have hgoal : ‖∑ i ∈ range (k' + 2), z ^ i‖ < (k' + 2 : ℝ) := by
              calc ‖∑ i ∈ range (k' + 2), z ^ i‖
                  = ‖1 + z + ∑ i ∈ Ico 2 (k' + 2), z ^ i‖ := by
                    rw [range_eq_Ico]
                    rw [sum_eq_sum_Ico_succ_bot (by omega : 0 < k' + 2)]
                    simp only [pow_zero]
                    rw [sum_eq_sum_Ico_succ_bot (by omega : 1 < k' + 2)]
                    simp only [pow_one]
                    ring_nf
                _ ≤ ‖(1 : ℂ) + z‖ + ‖∑ i ∈ Ico 2 (k' + 2), z ^ i‖ := norm_add_le _ _
                _ < 2 + ‖∑ i ∈ Ico 2 (k' + 2), z ^ i‖ := by linarith [h_one_plus_z]
                _ ≤ 2 + ∑ i ∈ Ico 2 (k' + 2), ‖z ^ i‖ := by
                    linarith [norm_sum_le (Ico 2 (k'+2)) (fun i => z^i)]
                _ = 2 + k' := by rw [hsum_bound]
                _ = (k' + 2 : ℝ) := by ring
            simp only [Nat.cast_add, Nat.cast_ofNat] at hgoal ⊢
            exact hgoal

-- Helper for the n = 1 case: f_1(z) = 1 for all z, so never zero
lemma fn_one_nonzero (z : ℂ) :
    (∑ i : Fin 1, ((1 : ℂ) - ↑(i : ℕ)) * z^(i : ℕ)) ≠ 0 := by
  simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, mul_one]
  norm_num

-- Main theorem: f_n has no roots in the closed unit disk
theorem Putnam_exercise_2018_b2 (n : ℕ) (hn : n > 0) (f : ℕ → ℂ → ℂ)
  (hf : ∀ n : ℕ, f n = λ (z : ℂ) => (∑ i : Fin n, (n-i)* z^(i : ℕ))) :
  ¬ (∃ z : ℂ, ‖z‖ ≤ 1 ∧ f n z = 0) := by
  -- Assume for contradiction that there exists z with |z| ≤ 1 and f_n(z) = 0
  intro ⟨z, hz, hfz⟩
  rw [hf] at hfz
  simp only at hfz

  -- Handle n = 1 separately: f_1(z) = 1 ≠ 0
  cases' n with m
  · omega  -- n > 0 contradicts n = 0

  cases' m with k
  · -- n = 1: f_1(z) = 1 ≠ 0
    -- For n = 1, the sum is just (1 - 0) * z^0 = 1
    -- The sum ∑ i : Fin 1, (↑(0 + 1) - ↑↑i) * z ^ ↑i evaluates to 1
    have heval : (∑ i : Fin 1, ((↑(0 + 1 : ℕ) : ℂ) - ↑(i : ℕ)) * z ^ (i : ℕ)) = 1 := by
      simp only [Fin.sum_univ_one, Fin.val_zero, Nat.cast_zero, sub_zero, pow_zero, mul_one]
      norm_cast
    exact one_ne_zero (heval ▸ hfz)

  -- Now n = k + 2 ≥ 2
  have hn2 : k + 2 ≥ 2 := by omega

  -- Case split on whether z = 1
  by_cases hz1 : z = 1
  · -- Case z = 1: f_n(1) > 0, contradiction
    rw [hz1] at hfz
    exact fn_at_one_ne_zero (k + 2) (by omega) hfz
  · -- Case z ≠ 1: use the key identity
    have hkey := key_identity (k + 2) z
    -- Since f_n(z) = 0, we have (z-1) * f_n(z) = (z-1) * 0 = 0
    rw [hfz, mul_zero] at hkey
    -- So ∑ z^{i+1} - n = 0, i.e., ∑ z^{i+1} = n
    have hsum_eq_n : ∑ i ∈ Finset.range (k + 2), z^(i + 1) = (↑(k + 2) : ℂ) := by
      have h : (0 : ℂ) = ∑ i ∈ range (k + 2), z ^ (i + 1) - ↑(k + 2) := hkey
      -- Solve algebraically in ℂ
      have h3 : ∑ i ∈ range (k + 2), z ^ (i + 1) - ↑(k + 2) = 0 := h.symm
      have h4 := sub_eq_zero.mp h3
      exact h4
    -- But |∑ z^{i+1}| < n by the bound lemma
    have hlt := sum_pow_norm_lt (k + 2) z hz hz1 hn2
    -- This contradicts |∑ z^{i+1}| = |n| = n
    have hcontra : ‖∑ i ∈ Finset.range (k + 2), z^(i + 1)‖ = (↑(k + 2) : ℝ) := by
      rw [hsum_eq_n]
      exact Complex.norm_natCast (k + 2)
    linarith
