import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Assume that $f$ is a continuous real function defined in $(a, b)$ such that $f\left(\frac{x+y}{2}\right) \leq \frac{f(x)+f(y)}{2}$ for all $x, y \in(a, b)$. Prove that $f$ is convex.
-/

/-Informal Proof

We shall prove that
$$
f(\lambda x+(1-\lambda) y) \leq \lambda f(x)+(1-\lambda) f(y)
$$
for all "dyadic rational" numbers, i.e., all numbers of the form $\lambda=\frac{k}{2^n}$, where $k$ is a nonnegative integer not larger than $2^n$. We do this by induction on $n$. The case $n=0$ is trivial (since $\lambda=0$ or $\lambda=1$ ). In the case $n=1$ we have $\lambda=0$ or $\lambda=1$ or $\lambda=\frac{1}{2}$. The first two cases are again trivial, and the third is precisely the hypothesis of the theorem. Suppose the result is proved for $n \leq r$, and consider $\lambda=\frac{k}{2^{r+1}}$. If $k$ is even, say $k=2 l$, then $\frac{k}{2^{r+1}}=\frac{l}{2^r}$, and we can appeal to the induction hypothesis. Now suppose $k$ is odd. Then $1 \leq k \leq 2^{r+1}-1$, and so the numbers $l=\frac{k-1}{2}$ and $m=\frac{k+1}{2}$ are integers with $0 \leq l<m \leq 2^r$. We can now write
$$
\lambda=\frac{s+t}{2},
$$
where $s=\frac{k-1}{2^{r+1}}=\frac{l}{2^r}$ and $t=\frac{k+1}{2^{r+1}}=\frac{m}{2^r}$. We then have
$$
\lambda x+(1-\lambda) y=\frac{[s x+(1-s) y]+[t x+(1-t) y]}{2}
$$
Hence by the hypothesis of the theorem and the induction hypothesis we have
$$
\begin{aligned}
f(\lambda x+(1-\lambda) y) & \leq \frac{f(s x+(1-s) y)+f(t x+(1-t) y)}{2} \\
& \leq \frac{s f(x)+(1-s) f(y)+t f(x)+(1-t) f(y)}{2} \\
&=\left(\frac{s+t}{2}\right) f(x)+\left(1-\frac{s+t}{2}\right) f(y) \\
&=\lambda f(x)+(1-\lambda) f(y)
\end{aligned}
$$
This completes the induction.
Now for each fixed $x$ and $y$ both sides of the inequality
$$
f(\lambda x+(1-\lambda) y) \leq \lambda f(x)+(1-\lambda) f(y)
$$
are continuous functions of $\lambda$. Hence the set on which this inequality holds (the inverse image of the closed set $[0, \infty)$ under the mapping $\lambda \mapsto \lambda f(x)+(1-$ $\lambda) f(y)-f(\lambda x+(1-\lambda) y))$ is a closed set. Since it contains all the points $\frac{k}{2^n}$, $0 \leq k \leq n, n=1,2, \ldots$, it must contain the closure of this set of points, i.e., it must contain all of $[0,1]$. Thus $f$ is convex.
-/

/-
  FORMAL PROOF OVERVIEW:
  ======================

  The proof follows three main steps:

  STEP 1: Show that the set S = {t ∈ [0,1] | f(t*x + (1-t)*y) ≤ t*f(x) + (1-t)*f(y)}
          is closed. This follows from continuity of f and algebraic operations.

  STEP 2: Prove by induction on n that all dyadic rationals k/2^n (0 ≤ k ≤ 2^n) satisfy
          the convexity inequality. The key cases are:
          - Base case (n=0): Only k=0,1, which give endpoints (trivial)
          - Inductive step: For k even, reduce to smaller n; for k odd, use midpoint
            convexity hypothesis with k-1 and k+1 (both even at level n)

  STEP 3: Show that any t ∈ [0,1] is in S by constructing a sequence of dyadic rationals
          ⌊t * 2^n⌋ / 2^n → t as n → ∞. Since each approximation is in S (by Step 2)
          and S is closed (by Step 1), the limit t must also be in S.
-/

theorem Rudin_exercise_4_24 {f : ℝ → ℝ}
  (hf : Continuous f) (a b : ℝ) (_hab : a < b)
  (h : ∀ x y : ℝ, a < x → x < b → a < y → y < b → f ((x + y) / 2) ≤ (f x + f y) / 2) :
  ConvexOn ℝ (Set.Ioo a b) f := by
  -- ConvexOn has two components: the set is convex, and the function satisfies Jensen's inequality
  constructor
  -- Part 1: The open interval (a,b) is convex (standard fact)
  · exact convex_Ioo a b

  -- Part 2: For all x, y in (a,b) and t, s ≥ 0 with t + s = 1,
  -- we need f(t*x + s*y) ≤ t*f(x) + s*f(y)
  intro x hx y hy t s ht hs hts
  simp only [smul_eq_mul]

  -- Since t + s = 1, we have s = 1 - t
  have hs_eq : s = 1 - t := by linarith

  -- STEP 1: Define S as the set of valid convex combination parameters
  -- S = {t' ∈ [0,1] | f(t'*x + (1-t')*y) ≤ t'*f(x) + (1-t')*f(y)}
  let S : Set ℝ := {t' | 0 ≤ t' ∧ t' ≤ 1 ∧
    f (t' * x + (1 - t') * y) ≤ t' * f x + (1 - t') * f y}

  -- Prove S is closed using continuity
  -- The set is the intersection of:
  -- - [0, ∞) (closed)
  -- - (-∞, 1] (closed)
  -- - {t' | f(...) ≤ ...} (preimage of closed set under continuous function)
  have hS_closed : IsClosed S := by
    have h1 : IsClosed {t' : ℝ | 0 ≤ t'} := isClosed_Ici
    have h2 : IsClosed {t' : ℝ | t' ≤ 1} := isClosed_Iic
    have h3 : IsClosed {t' : ℝ | f (t' * x + (1 - t') * y) ≤ t' * f x + (1 - t') * f y} := by
      -- This is the preimage of (-∞, 0] under the continuous map
      -- t' ↦ f(t'*x + (1-t')*y) - (t'*f(x) + (1-t')*f(y))
      apply isClosed_le
      · apply hf.comp; continuity  -- LHS is continuous
      · continuity  -- RHS is continuous (affine in t')
    -- S equals the intersection of these three closed sets
    have hS_eq : S = {t' | 0 ≤ t'} ∩ {t' | t' ≤ 1} ∩
        {t' | f (t' * x + (1 - t') * y) ≤ t' * f x + (1 - t') * f y} := by
      ext t'; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, S]; tauto
    rw [hS_eq]
    exact (h1.inter h2).inter h3

  -- STEP 2: Prove the convexity inequality holds for all dyadic rationals k/2^n
  -- hdyadic: For all n ≥ 0 and 0 ≤ k ≤ 2^n,
  --          f(k/2^n * x + (1 - k/2^n) * y) ≤ k/2^n * f(x) + (1 - k/2^n) * f(y)
  have hdyadic : ∀ n : ℕ, ∀ k : ℕ, k ≤ 2^n →
      f ((k : ℝ) / 2^n * x + (1 - (k : ℝ) / 2^n) * y) ≤
      (k : ℝ) / 2^n * f x + (1 - (k : ℝ) / 2^n) * f y := by
    intro n
    -- Induction on n (the "depth" of the dyadic rational)
    induction n with
    | zero =>
      -- Base case n = 0: only k = 0 or k = 1 are valid
      -- k/2^0 = k/1 = k, so k ∈ {0, 1}
      intro k hk
      interval_cases k
      · simp  -- k = 0: both sides equal f(y)
      · simp  -- k = 1: both sides equal f(x)
    | succ n ih =>
      -- Inductive step: assume true for 2^n, prove for 2^(n+1)
      intro k hk
      -- Case split on whether k is even or odd
      by_cases heven : Even k
      · -- Case: k is even, say k = 2m
        -- Then k/2^(n+1) = 2m/2^(n+1) = m/2^n
        -- So we can apply the induction hypothesis directly
        obtain ⟨m, hm_eq⟩ := heven
        have hm_le : m ≤ 2^n := by
          -- From k = 2m ≤ 2^(n+1) = 2 * 2^n, we get m ≤ 2^n
          have h1 : 2 * m ≤ 2^(n+1) := by
            rw [hm_eq] at hk; simp only [two_mul] at hk ⊢; exact hk
          simp only [pow_succ] at h1; omega
        -- Apply induction hypothesis at level n
        have ih_m := ih m hm_le
        -- Show that k/2^(n+1) = m/2^n (the fractions are equal)
        have hfrac_eq : (k : ℝ) / 2^(n+1) = (m : ℝ) / 2^n := by
          rw [hm_eq]
          simp only [pow_succ]
          field_simp
          push_cast
          ring
        -- Rewrite using this equality and apply ih
        rw [hfrac_eq]
        exact ih_m

      · -- Case: k is odd
        -- We use the midpoint convexity hypothesis
        -- Key idea: if k is odd, then (k-1)/2 and (k+1)/2 are integers with
        -- (k-1)/2 < k/2 < (k+1)/2, and k/2^(n+1) is the midpoint of
        -- (k-1)/2^(n+1) and (k+1)/2^(n+1)
        have hk_odd : Odd k := Nat.not_even_iff_odd.mp heven

        -- k is odd means k ≥ 1
        have hk_pos : 0 < k := Nat.pos_of_ne_zero fun h => by simp [h] at hk_odd

        -- k must be strictly less than 2^(n+1) (since k is odd and 2^(n+1) is even)
        have hk_lt : k < 2^(n+1) := by
          by_contra h_ge; push_neg at h_ge
          have h_eq : k = 2^(n+1) := le_antisymm hk h_ge
          rw [h_eq] at heven
          exact heven (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero n⟩)

        -- k-1 and k+1 are both even (since k is odd)
        have hk_sub_even : Even (k - 1) := by
          rcases hk_odd with ⟨j, hj⟩
          use j; omega
        have hk_add_even : Even (k + 1) := by
          rcases hk_odd with ⟨j, hj⟩
          use j + 1; omega

        -- Define l = (k-1)/2 and m = (k+1)/2
        let l := (k - 1) / 2
        let m := (k + 1) / 2

        -- These satisfy 2*l = k-1 and 2*m = k+1
        have hl_def : 2 * l = k - 1 := Nat.two_mul_div_two_of_even hk_sub_even
        have hm_def : 2 * m = k + 1 := Nat.two_mul_div_two_of_even hk_add_even

        have hlm : l < m := by omega

        -- Bound l and m by 2^n (so we can apply the induction hypothesis)
        have hl_le : l ≤ 2^n := by
          have h1 : 2 * l = k - 1 := hl_def
          have h2 : k ≤ 2^(n+1) := hk
          simp only [pow_succ] at h2; omega
        have hm_le : m ≤ 2^n := by
          have h1 : 2 * m = k + 1 := hm_def
          have h2 : k < 2^(n+1) := hk_lt
          simp only [pow_succ] at h2; omega

        -- Apply induction hypothesis to l/2^n and m/2^n
        have ih_l := ih l hl_le
        have ih_m := ih m hm_le

        -- Express l/2^n and m/2^n in terms of k
        -- l/2^n = (k-1)/2^(n+1) and m/2^n = (k+1)/2^(n+1)
        have hfrac_l : (l : ℝ) / 2^n = ((k : ℝ) - 1) / 2^(n+1) := by
          have h1 : (2 : ℝ) * l = k - 1 := by
            have hk_ge_1 : 1 ≤ k := hk_pos
            rw [← Nat.cast_two, ← Nat.cast_mul, hl_def]
            simp [Nat.cast_sub hk_ge_1]
          simp only [pow_succ]
          field_simp
          linarith

        have hfrac_m : (m : ℝ) / 2^n = ((k : ℝ) + 1) / 2^(n+1) := by
          have h1 : (2 : ℝ) * m = k + 1 := by
            rw [← Nat.cast_two, ← Nat.cast_mul, hm_def]; simp
          simp only [pow_succ]
          field_simp
          linarith

        -- k/2^(n+1) is the midpoint of l/2^n and m/2^n
        have hfrac_avg : (k : ℝ) / 2^(n+1) = ((l : ℝ) / 2^n + (m : ℝ) / 2^n) / 2 := by
          rw [hfrac_l, hfrac_m]; ring

        -- Verify that l/2^n and m/2^n are in [0, 1]
        have hl_nonneg : (0 : ℝ) ≤ (l : ℝ) / 2^n := by positivity
        have hl_le_one : (l : ℝ) / 2^n ≤ 1 := by
          rw [div_le_one (by positivity : (0 : ℝ) < 2^n)]
          have : (l : ℝ) ≤ (2^n : ℕ) := by exact_mod_cast hl_le
          simp at this ⊢; exact this
        have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) / 2^n := by positivity
        have hm_le_one : (m : ℝ) / 2^n ≤ 1 := by
          rw [div_le_one (by positivity : (0 : ℝ) < 2^n)]
          have : (m : ℝ) ≤ (2^n : ℕ) := by exact_mod_cast hm_le
          simp at this ⊢; exact this

        -- Define the two points p_l and p_m on the line segment [y, x]
        let p_l := (l : ℝ) / 2^n * x + (1 - (l : ℝ) / 2^n) * y
        let p_m := (m : ℝ) / 2^n * x + (1 - (m : ℝ) / 2^n) * y

        -- These points are in (a, b) since (a, b) is convex
        have hp_l_mem : p_l ∈ Set.Ioo a b :=
          convex_Ioo a b hx hy hl_nonneg (by linarith) (by ring)
        have hp_m_mem : p_m ∈ Set.Ioo a b :=
          convex_Ioo a b hx hy hm_nonneg (by linarith) (by ring)

        -- Apply the midpoint convexity hypothesis: f((p_l + p_m)/2) ≤ (f(p_l) + f(p_m))/2
        have hmid := h p_l p_m hp_l_mem.1 hp_l_mem.2 hp_m_mem.1 hp_m_mem.2

        -- The point (p_l + p_m)/2 equals k/2^(n+1) * x + (1 - k/2^(n+1)) * y
        have heq_mid : (p_l + p_m) / 2 = (k : ℝ) / 2^(n+1) * x + (1 - (k : ℝ) / 2^(n+1)) * y := by
          simp only [p_l, p_m]; rw [hfrac_avg]; ring

        -- We have l + m = k (as real numbers)
        have hsum : (l : ℝ) + m = k := by
          have h1 : 2 * l = k - 1 := hl_def
          have h2 : 2 * m = k + 1 := hm_def
          have hk_ge_1 : 1 ≤ k := hk_pos
          have h3 : (2 : ℝ) * l = k - 1 := by
            rw [← Nat.cast_two, ← Nat.cast_mul, h1]
            simp [Nat.cast_sub hk_ge_1]
          have h4 : (2 : ℝ) * m = k + 1 := by
            rw [← Nat.cast_two, ← Nat.cast_mul, h2]; simp
          linarith

        -- Now chain the inequalities:
        -- f(k/2^(n+1) * x + ...) = f((p_l + p_m)/2)
        --                       ≤ (f(p_l) + f(p_m))/2         [by midpoint convexity]
        --                       ≤ [(l/2^n)f(x) + ...]/2       [by induction hypothesis]
        --                       = k/2^(n+1) * f(x) + ...      [algebra]
        rw [← heq_mid]
        calc f ((p_l + p_m) / 2)
            ≤ (f p_l + f p_m) / 2 := hmid
          _ ≤ (((l : ℝ) / 2^n * f x + (1 - (l : ℝ) / 2^n) * f y) +
               ((m : ℝ) / 2^n * f x + (1 - (m : ℝ) / 2^n) * f y)) / 2 := by linarith
          _ = (k : ℝ) / 2^(n+1) * f x + (1 - (k : ℝ) / 2^(n+1)) * f y := by
              simp only [pow_succ]
              field_simp
              rw [← hsum]
              ring

  -- STEP 3: Show that t ∈ S by approximating t with dyadic rationals
  have ht_in_S : t ∈ S := by
    have ht_le_one : t ≤ 1 := by linarith

    -- Define the approximating sequence: approx(n) = ⌊t * 2^n⌋ / 2^n
    -- This is a dyadic rational that approximates t from below
    let approx : ℕ → ℝ := fun n => ⌊t * 2^n⌋ / 2^n

    -- Prove that approx(n) → t as n → ∞
    have happrox_tendsto : Filter.Tendsto approx Filter.atTop (nhds t) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      -- Find N such that (1/2)^N < ε
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1:ℝ)/2 < 1)
      use N
      intro n hn
      have h2n_pos : (0 : ℝ) < 2^n := by positivity
      -- Show |approx(n) - t| ≤ 1/2^n
      have hfloor_bound : |⌊t * 2^n⌋ / 2^n - t| ≤ 1 / 2^n := by
        -- Use floor properties: ⌊x⌋ ≤ x < ⌊x⌋ + 1
        have h1 : (⌊t * 2^n⌋ : ℝ) ≤ t * 2^n := Int.floor_le (t * 2^n)
        have h2 : t * 2^n - 1 < ⌊t * 2^n⌋ := Int.sub_one_lt_floor (t * 2^n)
        rw [abs_le]
        constructor
        · -- Lower bound: -(1/2^n) ≤ floor/2^n - t
          -- Equivalently: t - 1/2^n ≤ floor/2^n
          -- From h2: (t * 2^n - 1)/2^n < floor/2^n, and (t * 2^n - 1)/2^n = t - 1/2^n
          have hdiv : (⌊t * 2^n⌋ : ℝ) / 2^n > (t * 2^n - 1) / 2^n := by
            apply div_lt_div_of_pos_right h2 h2n_pos
          have heq : (t * 2^n - 1) / 2^n = t - 1 / 2^n := by
            field_simp
          linarith
        · -- Upper bound: floor/2^n - t ≤ 1/2^n
          -- Since floor ≤ actual value, floor/2^n ≤ t, so floor/2^n - t ≤ 0 ≤ 1/2^n
          have hdiv2 : (⌊t * 2^n⌋ : ℝ) / 2^n ≤ t := by
            have h3 : (⌊t * 2^n⌋ : ℝ) / 2^n ≤ (t * 2^n) / 2^n := by
              apply div_le_div_of_nonneg_right h1 (le_of_lt h2n_pos)
            have h4 : (t * 2^n) / 2^n = t := mul_div_cancel_right₀ t (ne_of_gt h2n_pos)
            linarith
          have hpos : (0 : ℝ) ≤ 1 / 2^n := by positivity
          calc (⌊t * 2^n⌋ : ℝ) / 2^n - t ≤ (0 : ℝ) := by linarith
            _ ≤ 1 / 2^n := hpos
      -- Chain: |approx(n) - t| ≤ 1/2^n = (1/2)^n ≤ (1/2)^N < ε
      calc dist (approx n) t = |approx n - t| := Real.dist_eq _ _
        _ ≤ 1 / 2^n := hfloor_bound
        _ = (1/2)^n := by rw [one_div, one_div, inv_pow]
        _ ≤ (1/2)^N := by
          -- Since n ≥ N and 0 < 1/2 ≤ 1, we have (1/2)^n ≤ (1/2)^N
          apply pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 ≤ 1)
          exact hn
        _ < ε := hN

    -- Prove that each approx(n) is in S (it's a dyadic rational)
    have happrox_in_S : ∀ n, approx n ∈ S := by
      intro n
      -- First show ⌊t * 2^n⌋ is non-negative
      have hfloor_nonneg : 0 ≤ ⌊t * 2^n⌋ := by
        apply Int.floor_nonneg.mpr
        apply mul_nonneg ht
        positivity

      have h2n_pos_real : (0 : ℝ) < 2^n := by positivity

      -- Show ⌊t * 2^n⌋ ≤ 2^n (as integers)
      have hfloor_le : ⌊t * 2^n⌋ ≤ (2^n : ℤ) := by
        have h1 : t * (2:ℝ)^n ≤ (2:ℝ)^n := by
          calc t * (2:ℝ)^n ≤ 1 * (2:ℝ)^n := mul_le_mul_of_nonneg_right ht_le_one (by positivity)
            _ = (2:ℝ)^n := one_mul _
        have h2 : (⌊t * 2^n⌋ : ℝ) ≤ t * 2^n := Int.floor_le _
        have h3 : (⌊t * 2^n⌋ : ℝ) ≤ (2:ℝ)^n := le_trans h2 h1
        -- floor(t * 2^n) ≤ 2^n as reals, and both are integers, so it holds as integers
        have h4 : (⌊t * 2^n⌋ : ℝ) ≤ ((2^n : ℤ) : ℝ) := by
          simp only [Int.cast_pow, Int.cast_ofNat]
          exact h3
        exact Int.cast_le.mp h4

      -- Convert ⌊t * 2^n⌋ to a natural number k
      let k := (⌊t * 2^n⌋).toNat
      have hk_eq : (k : ℤ) = ⌊t * 2^n⌋ := Int.toNat_of_nonneg hfloor_nonneg
      have hk_le : k ≤ 2^n := by
        have h1 : (k : ℤ) ≤ (2^n : ℤ) := by rw [hk_eq]; exact hfloor_le
        have h2 : (k : ℤ) ≤ ((2^n : ℕ) : ℤ) := by
          simp only [Nat.cast_pow, Nat.cast_ofNat] at h1 ⊢
          exact h1
        exact Nat.cast_le.mp (by exact_mod_cast h2)

      -- Apply the dyadic result to k/2^n
      have hdyadic_k := hdyadic n k hk_le

      -- Show approx(n) = k/2^n
      have happrox_eq : approx n = (k : ℝ) / 2^n := by
        simp only [approx]
        congr 1
        rw [← hk_eq]
        simp

      -- Conclude approx(n) ∈ S
      simp only [S, Set.mem_setOf_eq]
      rw [happrox_eq]
      refine ⟨by positivity, ?_, hdyadic_k⟩
      rw [div_le_one (by positivity : (0 : ℝ) < 2^n)]
      have : (k : ℝ) ≤ (2^n : ℕ) := by exact_mod_cast hk_le
      simp at this ⊢; exact this

    -- Since S is closed and approx(n) → t with all approx(n) ∈ S, we have t ∈ S
    exact hS_closed.mem_of_tendsto happrox_tendsto (Filter.Eventually.of_forall happrox_in_S)

  -- Extract the conclusion from t ∈ S
  simp only [S, Set.mem_setOf_eq] at ht_in_S
  have hfinal := ht_in_S.2.2
  rw [hs_eq]
  exact hfinal

/-
Corrected statement:
The original formalization uses `Continuous f` (global continuity on all of ℝ),
but the informal statement (Rudin Exercise 4.24) only assumes f is continuous
on the open interval (a, b).  Using `Continuous f` is a strictly stronger
hypothesis, making the original theorem logically weaker than the informal
claim (it applies to fewer functions).

The corrected version below replaces `Continuous f` with
`ContinuousOn f (Set.Ioo a b)`, which faithfully captures "f is a continuous
real function defined in (a, b)".
-/
theorem Rudin_exercise_4_24_corrected {f : ℝ → ℝ} {a b : ℝ}
  (hf : ContinuousOn f (Set.Ioo a b)) (_hab : a < b)
  (h : ∀ x y : ℝ, a < x → x < b → a < y → y < b → f ((x + y) / 2) ≤ (f x + f y) / 2) :
  ConvexOn ℝ (Set.Ioo a b) f := by
  -- Step 1: Split ConvexOn into (1) convexity of the set and (2) Jensen's inequality
  constructor
  -- Step 1.1: The open interval (a,b) is convex (standard Mathlib fact)
  · exact convex_Ioo a b
  -- Step 1.2: For all x, y ∈ (a,b) and t, s ≥ 0 with t + s = 1,
  --           show f(t•x + s•y) ≤ t•f(x) + s•f(y)
  intro x hx y hy t s ht hs hts
  simp only [smul_eq_mul]
  -- Step 1.3: Since t + s = 1, rewrite s = 1 - t for cleaner algebra
  have hs_eq : s = 1 - t := by linarith
  -- Step 2: Define the "valid parameters" set S
  --         S = {t' ∈ [0,1] | f(t'*x + (1-t')*y) ≤ t'*f(x) + (1-t')*f(y)}
  --         Our goal is to show t ∈ S.
  let S : Set ℝ := {t' | 0 ≤ t' ∧ t' ≤ 1 ∧
    f (t' * x + (1 - t') * y) ≤ t' * f x + (1 - t') * f y}
  -- Step 2.1: Establish that the affine map t' ↦ t'*x + (1-t')*y sends [0,1] into (a,b)
  --           This is needed because f is only continuous on (a,b), not all of ℝ.
  have hcomb_mem : ∀ t' : ℝ, 0 ≤ t' → t' ≤ 1 → t' * x + (1 - t') * y ∈ Set.Ioo a b :=
    fun t' ht' ht'1 => convex_Ioo a b hx hy ht' (by linarith) (by linarith)
  -- Step 3: Prove S is closed (this is the topological key to the argument)
  --         Strategy: write S = [0,1] ∩ g⁻¹((-∞, 0]) where
  --         g(t') = f(t'*x + (1-t')*y) - (t'*f(x) + (1-t')*f(y))
  --         is continuous on [0,1]. Then S is closed as the intersection of
  --         two closed sets: [0,1] (closed in ℝ) and the preimage of the closed
  --         set (-∞, 0] under a continuous-on-[0,1] function.
  have hS_closed : IsClosed S := by
    -- Step 3.1: The affine map t' ↦ t'*x + (1-t')*y is globally continuous
    have haffine_cont : Continuous (fun t' : ℝ => t' * x + (1 - t') * y) := by continuity
    -- Step 3.2: This affine map sends [0,1] into (a,b) (where f is continuous)
    have haffine_maps : Set.MapsTo (fun t' => t' * x + (1 - t') * y) (Set.Icc 0 1) (Set.Ioo a b) :=
      fun t' ht' => hcomb_mem t' ht'.1 ht'.2
    -- Step 3.3: Compose: f ∘ (affine map) is continuous on [0,1]
    --           Uses ContinuousOn.comp with the MapsTo condition
    have hf_comp_cont : ContinuousOn (fun t' => f (t' * x + (1 - t') * y)) (Set.Icc 0 1) :=
      (hf.comp haffine_cont.continuousOn haffine_maps)
    -- Step 3.4: The RHS t' ↦ t'*f(x) + (1-t')*f(y) is continuous on [0,1]
    --           (it's just an affine function of t', hence globally continuous)
    have hrhs_cont : ContinuousOn (fun t' => t' * f x + (1 - t') * f y) (Set.Icc 0 1) := by
      apply ContinuousOn.add
      · exact (continuousOn_id.mul continuousOn_const)
      · exact ((continuousOn_const.sub continuousOn_id).mul continuousOn_const)
    -- Step 3.5: The difference g(t') = LHS - RHS is continuous on [0,1]
    have hg_cont : ContinuousOn (fun t' => f (t' * x + (1 - t') * y) - (t' * f x + (1 - t') * f y)) (Set.Icc 0 1) :=
      hf_comp_cont.sub hrhs_cont
    -- Step 3.6: Rewrite S as [0,1] ∩ g⁻¹((-∞, 0])
    --           The condition f(...) ≤ ... is equivalent to g(t') ≤ 0
    have hS_eq : S = Set.Icc 0 1 ∩ (fun t' => f (t' * x + (1 - t') * y) - (t' * f x + (1 - t') * f y)) ⁻¹' Set.Iic 0 := by
      ext t'; simp only [S, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Icc, sub_nonpos]; tauto
    rw [hS_eq]
    -- Step 3.7: Apply ContinuousOn.preimage_isClosed_of_isClosed:
    --           g continuous on closed set [0,1], and (-∞, 0] is closed,
    --           so [0,1] ∩ g⁻¹((-∞, 0]) is closed.
    exact hg_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  -- Step 4: Prove the convexity inequality holds for all dyadic rationals k/2^n
  --         by induction on n (the "depth" of the dyadic rational).
  --         This is the combinatorial core of the proof.
  have hdyadic : ∀ n : ℕ, ∀ k : ℕ, k ≤ 2^n →
      f ((k : ℝ) / 2^n * x + (1 - (k : ℝ) / 2^n) * y) ≤
      (k : ℝ) / 2^n * f x + (1 - (k : ℝ) / 2^n) * f y := by
    intro n
    induction n with
    | zero =>
      -- Step 4.1: Base case n = 0. Only k = 0 and k = 1 are valid (since k ≤ 2^0 = 1).
      --           k = 0: both sides reduce to f(y) ≤ f(y) (trivial)
      --           k = 1: both sides reduce to f(x) ≤ f(x) (trivial)
      intro k hk; interval_cases k <;> simp
    | succ n ih =>
      -- Step 4.2: Inductive step. Assume the result holds for all k'/2^n with k' ≤ 2^n.
      --           Prove it for k/2^(n+1) with k ≤ 2^(n+1).
      intro k hk
      by_cases heven : Even k
      · -- Step 4.2.1: Case k even, k = 2m.
        --             Then k/2^(n+1) = 2m/2^(n+1) = m/2^n, and m ≤ 2^n,
        --             so the induction hypothesis applies directly.
        obtain ⟨m, hm_eq⟩ := heven
        have hm_le : m ≤ 2^n := by
          have h1 : 2 * m ≤ 2^(n+1) := by rw [hm_eq] at hk; simp only [two_mul] at hk ⊢; exact hk
          simp only [pow_succ] at h1; omega
        -- Step 4.2.1.1: Show the fraction equality k/2^(n+1) = m/2^n
        have hfrac_eq : (k : ℝ) / 2^(n+1) = (m : ℝ) / 2^n := by
          rw [hm_eq]; simp only [pow_succ]; field_simp; push_cast; ring
        -- Step 4.2.1.2: Rewrite and apply induction hypothesis
        rw [hfrac_eq]; exact ih m hm_le
      · -- Step 4.2.2: Case k odd. This is the non-trivial case that uses the
        --             midpoint convexity hypothesis.
        --             Key idea: k/2^(n+1) is the midpoint of (k-1)/2^(n+1) and (k+1)/2^(n+1),
        --             which equal l/2^n and m/2^n respectively (where l=(k-1)/2, m=(k+1)/2).
        have hk_odd : Odd k := Nat.not_even_iff_odd.mp heven
        -- Step 4.2.2.1: k is odd ⟹ k ≥ 1
        have hk_pos : 0 < k := Nat.pos_of_ne_zero fun h => by simp [h] at hk_odd
        -- Step 4.2.2.2: k is odd and k ≤ 2^(n+1) ⟹ k < 2^(n+1)
        --               (since 2^(n+1) is even, k can't equal it)
        have hk_lt : k < 2^(n+1) := by
          by_contra h_ge; push_neg at h_ge
          have h_eq : k = 2^(n+1) := le_antisymm hk h_ge
          rw [h_eq] at heven; exact heven (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero n⟩)
        -- Step 4.2.2.3: k-1 and k+1 are both even (since k is odd)
        have hk_sub_even : Even (k - 1) := by rcases hk_odd with ⟨j, hj⟩; use j; omega
        have hk_add_even : Even (k + 1) := by rcases hk_odd with ⟨j, hj⟩; use j + 1; omega
        -- Step 4.2.2.4: Define l = (k-1)/2 and m = (k+1)/2
        let l := (k - 1) / 2
        let m := (k + 1) / 2
        -- Step 4.2.2.5: Verify 2*l = k-1 and 2*m = k+1
        have hl_def : 2 * l = k - 1 := Nat.two_mul_div_two_of_even hk_sub_even
        have hm_def : 2 * m = k + 1 := Nat.two_mul_div_two_of_even hk_add_even
        -- Step 4.2.2.6: Bound l ≤ 2^n and m ≤ 2^n (needed to apply induction hypothesis)
        have hl_le : l ≤ 2^n := by simp only [pow_succ] at hk; omega
        have hm_le : m ≤ 2^n := by
          have h2 : k < 2^(n+1) := hk_lt; simp only [pow_succ] at h2; omega
        -- Step 4.2.2.7: Apply induction hypothesis to l/2^n and m/2^n
        have ih_l := ih l hl_le
        have ih_m := ih m hm_le
        -- Step 4.2.2.8: Express l/2^n = (k-1)/2^(n+1) and m/2^n = (k+1)/2^(n+1)
        have hfrac_l : (l : ℝ) / 2^n = ((k : ℝ) - 1) / 2^(n+1) := by
          have h1 : (2 : ℝ) * l = k - 1 := by
            rw [← Nat.cast_two, ← Nat.cast_mul, hl_def]; simp [Nat.cast_sub hk_pos]
          simp only [pow_succ]; field_simp; linarith
        have hfrac_m : (m : ℝ) / 2^n = ((k : ℝ) + 1) / 2^(n+1) := by
          have h1 : (2 : ℝ) * m = k + 1 := by
            rw [← Nat.cast_two, ← Nat.cast_mul, hm_def]; simp
          simp only [pow_succ]; field_simp; linarith
        -- Step 4.2.2.9: k/2^(n+1) is the average of l/2^n and m/2^n
        have hfrac_avg : (k : ℝ) / 2^(n+1) = ((l : ℝ) / 2^n + (m : ℝ) / 2^n) / 2 := by
          rw [hfrac_l, hfrac_m]; ring
        -- Step 4.2.2.10: Verify l/2^n ∈ [0,1] and m/2^n ∈ [0,1]
        have hl_nonneg : (0 : ℝ) ≤ (l : ℝ) / 2^n := by positivity
        have hl_le_one : (l : ℝ) / 2^n ≤ 1 := by
          rw [div_le_one (by positivity : (0 : ℝ) < 2^n)]
          have : (l : ℝ) ≤ (2^n : ℕ) := by exact_mod_cast hl_le
          simp at this ⊢; exact this
        have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) / 2^n := by positivity
        have hm_le_one : (m : ℝ) / 2^n ≤ 1 := by
          rw [div_le_one (by positivity : (0 : ℝ) < 2^n)]
          have : (m : ℝ) ≤ (2^n : ℕ) := by exact_mod_cast hm_le
          simp at this ⊢; exact this
        -- Step 4.2.2.11: Define the two interpolation points
        --                p_l = (l/2^n)*x + (1 - l/2^n)*y  (the "left" point)
        --                p_m = (m/2^n)*x + (1 - m/2^n)*y  (the "right" point)
        let p_l := (l : ℝ) / 2^n * x + (1 - (l : ℝ) / 2^n) * y
        let p_m := (m : ℝ) / 2^n * x + (1 - (m : ℝ) / 2^n) * y
        -- Step 4.2.2.12: Show p_l, p_m ∈ (a,b) (since (a,b) is convex and x, y ∈ (a,b))
        have hp_l_mem : p_l ∈ Set.Ioo a b :=
          convex_Ioo a b hx hy hl_nonneg (by linarith) (by ring)
        have hp_m_mem : p_m ∈ Set.Ioo a b :=
          convex_Ioo a b hx hy hm_nonneg (by linarith) (by ring)
        -- Step 4.2.2.13: Apply midpoint convexity hypothesis to p_l and p_m
        --                Result: f((p_l + p_m)/2) ≤ (f(p_l) + f(p_m))/2
        have hmid := h p_l p_m hp_l_mem.1 hp_l_mem.2 hp_m_mem.1 hp_m_mem.2
        -- Step 4.2.2.14: Show (p_l + p_m)/2 = k/2^(n+1) * x + (1 - k/2^(n+1)) * y
        --                (the target point equals the midpoint of p_l and p_m)
        have heq_mid : (p_l + p_m) / 2 = (k : ℝ) / 2^(n+1) * x + (1 - (k : ℝ) / 2^(n+1)) * y := by
          simp only [p_l, p_m]; rw [hfrac_avg]; ring
        -- Step 4.2.2.15: Establish l + m = k (as reals) for the final algebra step
        have hsum : (l : ℝ) + m = k := by
          have h1 : 2 * l = k - 1 := hl_def
          have h2 : 2 * m = k + 1 := hm_def
          have h3 : (2 : ℝ) * l = k - 1 := by
            rw [← Nat.cast_two, ← Nat.cast_mul, h1]; simp [Nat.cast_sub hk_pos]
          have h4 : (2 : ℝ) * m = k + 1 := by
            rw [← Nat.cast_two, ← Nat.cast_mul, h2]; simp
          linarith
        -- Step 4.2.2.16: Chain the inequalities together:
        --   f(k/2^(n+1) * x + ...)
        --   = f((p_l + p_m)/2)                             [by heq_mid]
        --   ≤ (f(p_l) + f(p_m))/2                         [by midpoint hypothesis]
        --   ≤ ((l/2^n)*f(x) + ... + (m/2^n)*f(x) + ...)/2  [by IH at l and m]
        --   = (k/2^(n+1))*f(x) + (1 - k/2^(n+1))*f(y)    [by algebra using l+m=k]
        rw [← heq_mid]
        calc f ((p_l + p_m) / 2)
            ≤ (f p_l + f p_m) / 2 := hmid
          _ ≤ (((l : ℝ) / 2^n * f x + (1 - (l : ℝ) / 2^n) * f y) +
               ((m : ℝ) / 2^n * f x + (1 - (m : ℝ) / 2^n) * f y)) / 2 := by linarith
          _ = (k : ℝ) / 2^(n+1) * f x + (1 - (k : ℝ) / 2^(n+1)) * f y := by
              simp only [pow_succ]; field_simp; rw [← hsum]; ring
  -- Step 5: Show t ∈ S by approximating t with dyadic rationals from Step 4
  --         Strategy: construct a sequence of dyadic rationals converging to t,
  --         show they're all in S (by Step 4), then use closedness of S (Step 3).
  have ht_in_S : t ∈ S := by
    have ht_le_one : t ≤ 1 := by linarith
    -- Step 5.1: Define the approximating sequence: approx(n) = ⌊t * 2^n⌋ / 2^n
    --           This rounds t down to the nearest dyadic rational of depth n.
    let approx : ℕ → ℝ := fun n => ⌊t * 2^n⌋ / 2^n
    -- Step 5.2: Prove approx(n) → t as n → ∞
    --           The error |approx(n) - t| ≤ 1/2^n → 0.
    have happrox_tendsto : Filter.Tendsto approx Filter.atTop (nhds t) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      -- Step 5.2.1: Find N such that (1/2)^N < ε
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1:ℝ)/2 < 1)
      use N
      intro n hn
      have h2n_pos : (0 : ℝ) < 2^n := by positivity
      -- Step 5.2.2: Show |⌊t * 2^n⌋ / 2^n - t| ≤ 1/2^n using floor properties
      --             Key facts: ⌊x⌋ ≤ x (so approx(n) ≤ t) and x - 1 < ⌊x⌋ (so t - 1/2^n < approx(n))
      have hfloor_bound : |⌊t * 2^n⌋ / 2^n - t| ≤ 1 / 2^n := by
        have h1 : (⌊t * 2^n⌋ : ℝ) ≤ t * 2^n := Int.floor_le (t * 2^n)
        have h2 : t * 2^n - 1 < ⌊t * 2^n⌋ := Int.sub_one_lt_floor (t * 2^n)
        rw [abs_le]
        constructor
        · -- Step 5.2.2.1: Lower bound: -(1/2^n) ≤ ⌊t*2^n⌋/2^n - t
          --               From x - 1 < ⌊x⌋, dividing by 2^n gives t - 1/2^n < approx(n)
          have hdiv : (⌊t * 2^n⌋ : ℝ) / 2^n > (t * 2^n - 1) / 2^n :=
            div_lt_div_of_pos_right h2 h2n_pos
          have heq : (t * 2^n - 1) / 2^n = t - 1 / 2^n := by field_simp
          linarith
        · -- Step 5.2.2.2: Upper bound: ⌊t*2^n⌋/2^n - t ≤ 1/2^n
          --               Since ⌊x⌋ ≤ x, we have approx(n) ≤ t, so the difference is ≤ 0 ≤ 1/2^n
          have hdiv2 : (⌊t * 2^n⌋ : ℝ) / 2^n ≤ t := by
            have h3 : (⌊t * 2^n⌋ : ℝ) / 2^n ≤ (t * 2^n) / 2^n :=
              div_le_div_of_nonneg_right h1 (le_of_lt h2n_pos)
            have h4 : (t * 2^n) / 2^n = t := mul_div_cancel_right₀ t (ne_of_gt h2n_pos)
            linarith
          linarith [show (0 : ℝ) ≤ 1 / 2^n from by positivity]
      -- Step 5.2.3: Chain: dist(approx(n), t) ≤ 1/2^n = (1/2)^n ≤ (1/2)^N < ε
      calc dist (approx n) t = |approx n - t| := Real.dist_eq _ _
        _ ≤ 1 / 2^n := hfloor_bound
        _ = (1/2)^n := by rw [one_div, one_div, inv_pow]
        _ ≤ (1/2)^N := by
          apply pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 ≤ 1)
          exact hn
        _ < ε := hN
    -- Step 5.3: Prove each approx(n) ∈ S
    --           Each approx(n) = k/2^n for some k ≤ 2^n, so Step 4 applies.
    have happrox_in_S : ∀ n, approx n ∈ S := by
      intro n
      -- Step 5.3.1: Show ⌊t * 2^n⌋ ≥ 0 (since t ≥ 0 and 2^n > 0)
      have hfloor_nonneg : 0 ≤ ⌊t * 2^n⌋ := by
        apply Int.floor_nonneg.mpr; apply mul_nonneg ht; positivity
      have h2n_pos_real : (0 : ℝ) < 2^n := by positivity
      -- Step 5.3.2: Show ⌊t * 2^n⌋ ≤ 2^n (since t ≤ 1 implies t*2^n ≤ 2^n)
      have hfloor_le : ⌊t * 2^n⌋ ≤ (2^n : ℤ) := by
        have h1 : t * (2:ℝ)^n ≤ (2:ℝ)^n := by
          calc t * (2:ℝ)^n ≤ 1 * (2:ℝ)^n := mul_le_mul_of_nonneg_right ht_le_one (by positivity)
            _ = (2:ℝ)^n := one_mul _
        have h2 : (⌊t * 2^n⌋ : ℝ) ≤ t * 2^n := Int.floor_le _
        have h3 : (⌊t * 2^n⌋ : ℝ) ≤ (2:ℝ)^n := le_trans h2 h1
        have h4 : (⌊t * 2^n⌋ : ℝ) ≤ ((2^n : ℤ) : ℝ) := by
          simp only [Int.cast_pow, Int.cast_ofNat]; exact h3
        exact Int.cast_le.mp h4
      -- Step 5.3.3: Convert the integer floor to a natural number k
      --             (safe since floor is non-negative)
      let k := (⌊t * 2^n⌋).toNat
      have hk_eq : (k : ℤ) = ⌊t * 2^n⌋ := Int.toNat_of_nonneg hfloor_nonneg
      -- Step 5.3.4: Show k ≤ 2^n as natural numbers
      have hk_le : k ≤ 2^n := by
        have h1 : (k : ℤ) ≤ (2^n : ℤ) := by rw [hk_eq]; exact hfloor_le
        have h2 : (k : ℤ) ≤ ((2^n : ℕ) : ℤ) := by
          simp only [Nat.cast_pow, Nat.cast_ofNat] at h1 ⊢; exact h1
        exact Nat.cast_le.mp (by exact_mod_cast h2)
      -- Step 5.3.5: Apply the dyadic result (Step 4) to k/2^n
      have hdyadic_k := hdyadic n k hk_le
      -- Step 5.3.6: Show approx(n) = k/2^n (just unfolding definitions)
      have happrox_eq : approx n = (k : ℝ) / 2^n := by
        simp only [approx]; congr 1; rw [← hk_eq]; simp
      -- Step 5.3.7: Conclude approx(n) ∈ S by verifying all three conditions:
      --             0 ≤ k/2^n, k/2^n ≤ 1, and the convexity inequality (from hdyadic_k)
      simp only [S, Set.mem_setOf_eq]
      rw [happrox_eq]
      refine ⟨by positivity, ?_, hdyadic_k⟩
      rw [div_le_one (by positivity : (0 : ℝ) < 2^n)]
      have : (k : ℝ) ≤ (2^n : ℕ) := by exact_mod_cast hk_le
      simp at this ⊢; exact this
    -- Step 5.4: Conclude t ∈ S using:
    --           - S is closed (Step 3)
    --           - approx(n) → t (Step 5.2)
    --           - approx(n) ∈ S for all n (Step 5.3)
    --           By the definition of closed sets, the limit of a sequence in S is in S.
    exact hS_closed.mem_of_tendsto happrox_tendsto (Filter.Eventually.of_forall happrox_in_S)
  -- Step 6: Extract the final inequality from t ∈ S and substitute s = 1 - t
  simp only [S, Set.mem_setOf_eq] at ht_in_S
  rw [hs_eq]; exact ht_in_S.2.2
