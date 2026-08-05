import Mathlib

open scoped BigOperators
open Real Nat Function

/-Informal Statement

Given a real number $a$, we define a sequence by $x_{0}=1$, $x_{1}=x_{2}=a$, and $x_{n+1}=2 x_{n} x_{n-1}-x_{n-2}$ for $n \geq 2$. Prove that if $x_{n}=0$ for some $n$, then the sequence is periodic.
-/

/-Informal Proof

We first rule out the case $|a|>1$. In this case, we prove that $|x_{n+1}| \geq |x_n|$ for all $n$, meaning that we cannot have $x_n = 0$. We proceed by induction; the claim is true for $n=0,1$ by hypothesis. To prove the claim for  $n \geq 2$, write
\begin{align*}
|x_{n+1}| &= |2x_nx_{n-1}-x_{n-2}| \\
&\geq 2|x_n||x_{n-1}|-|x_{n-2}| \\
&\geq |x_n|(2|x_{n-1}|-1) \geq |x_n|,
\end{align*}
where the last step follows from $|x_{n-1}| \geq |x_{n-2}| \geq \cdots \geq |x_0| = 1$.

We may thus assume hereafter that $|a|\leq 1$. We can then write $a = \cos b$ for some $b \in [0,\pi]$.
Let $\{F_n\}$ be the Fibonacci sequence, defined as usual by $F_1=F_2=1$ and $F_{n+1}=F_n+F_{n-1}$. We show by induction that
\[
x_n = \cos(F_n b) \qquad (n \geq 0).
\]
Indeed, this is true for $n=0,1,2$; given that it is true for $n \leq m$, then
\begin{align*}
2x_mx_{m-1}&=2\cos(F_mb)\cos(F_{m-1}b) \\
&= \cos((F_m-F_{m-1})b)+\cos((F_m+F_{m-1})b) \\
&= \cos(F_{m-2}b)+\cos(F_{m+1}b)
\end{align*}
and so
$x_{m+1} = 2x_mx_{m-1}-x_{m-2} = \cos(F_{m+1}b)$. This completes the induction.


Since $x_n = \cos(F_n b)$, if $x_n=0$ for some $n$ then $F_n b = \frac{k}{2} \pi$ for some odd integer $k$. In particular, we can write $b = \frac{c}{d}(2\pi)$ where $c = k$ and $d = 4F_n$ are integers.


Let $x_n$ denote the pair $(F_n,F_{n+1})$, where each entry in this pair is viewed as an element of $\mathbb{Z}/d\mathbb{Z}$. Since there are only finitely many possibilities for $x_n$, there must be some $n_2>n_1$ such that $x_{n_1}=x_{n_2}$. Now $x_n$ uniquely determines both $x_{n+1}$ and $x_{n-1}$, and it follows that the sequence $\{x_n\}$ is periodic: for $\ell = n_2-n_1$, $x_{n+\ell} = x_n$ for all $n \geq 0$. In particular, $F_{n+\ell} \equiv F_n \pmod{d}$ for all $n$. But then $\frac{F_{n+\ell}c}{d}-\frac{F_n c}{d}$ is an integer, and so
\begin{align*}
x_{n+\ell} &= \cos\left(\frac{F_{n+\ell}c}{d}(2\pi)\right)\\
& = \cos\left(\frac{F_n c}{d}(2\pi)\right) = x_n
\end{align*}
for all $n$. Thus the sequence $\{x_n\}$ is periodic, as desired.
-/


/-!
# Putnam 2018 B4: Periodicity of a recurrence relation

## Overview
Given a = cos(b) for |a| ≤ 1, the sequence x_n = cos(F_n · b) where F_n is Fibonacci.
If x_n = 0, then F_n · b = (2k+1)π/2, making b a rational multiple of π.
The Fibonacci sequence mod m is periodic (Pisano period), so x is periodic.
For |a| > 1, |x_n| ≥ 1 always, so x_n ≠ 0 (vacuously true).
-/

-- ============================================================================
-- Step 1: Helper lemma for modular subtraction (needed for Pisano period proof)
-- ============================================================================
lemma sub_mod_eq' (a b m : ℕ) (hm : m > 0) (hab : b ≤ a) :
    (a - b) % m = (a % m + m - b % m) % m := by
  have hbm : b % m < m := Nat.mod_lt _ hm
  have ham : a % m < m := Nat.mod_lt _ hm
  have hle : b % m ≤ a % m + m := by omega
  have key : (↑(a - b) : ℤ) % ↑m = (↑(a % m) - ↑(b % m)) % ↑m := by
    rw [Int.ofNat_sub hab, Int.sub_emod]
    simp only [Int.ofNat_mod_ofNat]
  have key2 : (↑(a % m) - ↑(b % m) : ℤ) % ↑m = (↑(a % m) + ↑m - ↑(b % m)) % ↑m := by
    have h1 : (↑(a % m) + ↑m - ↑(b % m) : ℤ) = ↑(a % m) - ↑(b % m) + ↑m := by ring
    rw [h1]; symm
    have := Int.add_mul_emod_self_right (↑(a % m) - ↑(b % m)) 1 ↑m
    simp only [one_mul] at this; exact this
  have key3 : (↑(a % m) + ↑m - ↑(b % m) : ℤ) = ↑(a % m + m - b % m) := by
    rw [Int.ofNat_sub hle]; simp only [Int.natCast_add]
  have final : (↑(a - b) : ℤ) % ↑m = (↑(a % m + m - b % m) : ℤ) % ↑m := by rw [key, key2, key3]
  simp only [Int.ofNat_mod_ofNat, Nat.cast_inj] at final; exact final

-- ============================================================================
-- Step 2: Pisano periodicity (Fibonacci mod m is periodic)
-- ============================================================================
lemma fib_mod_periodic' (m : ℕ) (hm : m > 0) :
    ∃ k : ℕ, k > 0 ∧ ∀ n : ℕ, fib (n + k) % m = fib n % m := by
  classical
  -- Step 2.1: Define pairs (F_n mod m, F_{n+1} mod m)
  let P : ℕ → Fin m × Fin m := fun n => (⟨fib n % m, Nat.mod_lt _ hm⟩, ⟨fib (n + 1) % m, Nat.mod_lt _ hm⟩)
  -- Step 2.2: By pigeonhole, some pair repeats
  have h_pigeonhole : ∃ i j, i < j ∧ P i = P j := by
    by_contra h_contra; push_neg at h_contra
    have h_inj : Function.Injective (fun i : Fin (m * m + 1) => P i.val) := by
      intro ⟨i, hi⟩ ⟨j, hj⟩ heq; simp only at heq
      by_cases hij : i = j
      · simp [hij]
      · rcases lt_trichotomy i j with h | h | h
        · exact absurd heq (h_contra i j h)
        · exact absurd h hij
        · exact absurd heq.symm (h_contra j i h)
    have h_card_target : Fintype.card (Fin m × Fin m) = m * m := by simp [Fintype.card_prod, Fintype.card_fin]
    have h_le := Fintype.card_le_of_injective _ h_inj
    simp only [Fintype.card_fin, h_card_target] at h_le; omega
  -- Step 2.3: Extract the period
  obtain ⟨i, j, hij, hP⟩ := h_pigeonhole
  use j - i
  constructor; · omega
  · have heq_fib : fib i % m = fib j % m ∧ fib (i + 1) % m = fib (j + 1) % m := by
      simp only [P, Prod.ext_iff, Fin.ext_iff] at hP; exact hP
    -- Step 2.4: Forward induction
    have forward : ∀ n, fib (i + n) % m = fib (j + n) % m := by
      intro n; induction n using Nat.strong_induction_on with | _ n ih =>
        match n with
        | 0 => simp [heq_fib.1]
        | 1 => exact heq_fib.2
        | n' + 2 =>
          have hi2 : fib (i + (n' + 2)) = fib (i + n') + fib (i + n' + 1) := by
            have eq1 : i + (n' + 2) = (i + n') + 2 := by omega
            rw [eq1, fib_add_two]
          have hj2 : fib (j + (n' + 2)) = fib (j + n') + fib (j + n' + 1) := by
            have eq1 : j + (n' + 2) = (j + n') + 2 := by omega
            rw [eq1, fib_add_two]
          have ih1 := ih n' (by omega); have ih2 := ih (n' + 1) (by omega)
          have ih2' : fib (i + n' + 1) % m = fib (j + n' + 1) % m := by
            have eq1 : i + n' + 1 = i + (n' + 1) := by omega
            have eq2 : j + n' + 1 = j + (n' + 1) := by omega
            rw [eq1, eq2]; exact ih2
          calc fib (i + (n' + 2)) % m = (fib (i + n') + fib (i + n' + 1)) % m := by rw [hi2]
            _ = (fib (i + n') % m + fib (i + n' + 1) % m) % m := by rw [Nat.add_mod]
            _ = (fib (j + n') % m + fib (j + n' + 1) % m) % m := by rw [ih1, ih2']
            _ = (fib (j + n') + fib (j + n' + 1)) % m := by rw [← Nat.add_mod]
            _ = fib (j + (n' + 2)) % m := by rw [hj2]
    -- Step 2.5: Backward induction
    have backward : ∀ n ≤ i, fib (i - n) % m = fib (j - n) % m := by
      intro n hn; induction n using Nat.strong_induction_on with | _ n ih =>
        match n with
        | 0 => simp only [Nat.sub_zero]; exact heq_fib.1
        | 1 =>
          have hi_eq : fib (i - 1) + fib i = fib (i + 1) := by
            have eq1 : i - 1 + 2 = i + 1 := by omega
            have eq2 : i - 1 + 1 = i := by omega
            have := fib_add_two (n := i - 1); rw [eq1, eq2] at this; exact this.symm
          have hj_eq : fib (j - 1) + fib j = fib (j + 1) := by
            have eq1 : j - 1 + 2 = j + 1 := by omega
            have eq2 : j - 1 + 1 = j := by omega
            have := fib_add_two (n := j - 1); rw [eq1, eq2] at this; exact this.symm
          have h_i1 : fib (i - 1) = fib (i + 1) - fib i := by omega
          have h_j1 : fib (j - 1) = fib (j + 1) - fib j := by omega
          rw [h_i1, h_j1]
          calc (fib (i + 1) - fib i) % m
              = (fib (i + 1) % m + m - fib i % m) % m := sub_mod_eq' _ _ _ hm (fib_mono (by omega))
            _ = (fib (j + 1) % m + m - fib j % m) % m := by rw [heq_fib.1, heq_fib.2]
            _ = (fib (j + 1) - fib j) % m := (sub_mod_eq' _ _ _ hm (fib_mono (by omega))).symm
        | n' + 2 =>
          have ih1 := ih (n' + 1) (by omega) (by omega); have ih0 := ih n' (by omega) (by omega)
          have hi_eq : fib (i - (n' + 2)) + fib (i - (n' + 1)) = fib (i - n') := by
            have eq1 : i - (n' + 2) + 2 = i - n' := by omega
            have eq2 : i - (n' + 2) + 1 = i - (n' + 1) := by omega
            have := fib_add_two (n := i - (n' + 2)); rw [eq1, eq2] at this; exact this.symm
          have hj_eq : fib (j - (n' + 2)) + fib (j - (n' + 1)) = fib (j - n') := by
            have eq1 : j - (n' + 2) + 2 = j - n' := by omega
            have eq2 : j - (n' + 2) + 1 = j - (n' + 1) := by omega
            have := fib_add_two (n := j - (n' + 2)); rw [eq1, eq2] at this; exact this.symm
          have h_i2 : fib (i - (n' + 2)) = fib (i - n') - fib (i - (n' + 1)) := by omega
          have h_j2 : fib (j - (n' + 2)) = fib (j - n') - fib (j - (n' + 1)) := by omega
          rw [h_i2, h_j2]
          calc (fib (i - n') - fib (i - (n' + 1))) % m
              = (fib (i - n') % m + m - fib (i - (n' + 1)) % m) % m := sub_mod_eq' _ _ _ hm (fib_mono (by omega))
            _ = (fib (j - n') % m + m - fib (j - (n' + 1)) % m) % m := by rw [ih0, ih1]
            _ = (fib (j - n') - fib (j - (n' + 1))) % m := (sub_mod_eq' _ _ _ hm (fib_mono (by omega))).symm
    -- Step 2.6: Combine forward and backward
    intro n
    by_cases hn : n ≤ i
    · have h := backward (i - n) (by omega)
      have h1 : i - (i - n) = n := by omega
      have h2 : j - (i - n) = n + (j - i) := by omega
      rw [h1, h2] at h; exact h.symm
    · push_neg at hn; have h := forward (n - i)
      have h1 : i + (n - i) = n := by omega
      have h2 : j + (n - i) = n + (j - i) := by omega
      rw [h1, h2] at h; exact h.symm

-- ============================================================================
-- Step 3: Cosine product-to-sum formula
-- ============================================================================
lemma cos_prod_to_sum' (A B : ℝ) : 2 * cos A * cos B = cos (A - B) + cos (A + B) := by
  have h1 : cos (A - B) = cos A * cos B + sin A * sin B := cos_sub A B
  have h2 : cos (A + B) = cos A * cos B - sin A * sin B := cos_add A B
  linarith

-- ============================================================================
-- Step 4: Fibonacci recurrence lemmas
-- ============================================================================
lemma fib_sub_nat' (n : ℕ) (hn : n ≥ 2) : fib n - fib (n - 1) = fib (n - 2) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn; subst hk
  have h1 : 2 + k - 1 = k + 1 := by omega
  have h2 : 2 + k - 2 = k := by omega
  rw [h1, h2]
  have h3 : fib (2 + k) = fib k + fib (k + 1) := by
    have : 2 + k = k + 2 := by omega
    rw [this, fib_add_two]
  omega

lemma fib_add_for_rec' (n : ℕ) (hn : n ≥ 1) : fib (n - 1) + fib n = fib (n + 1) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn; subst hk
  have h1 : 1 + k - 1 = k := by omega
  have h2 : 1 + k + 1 = k + 2 := by omega
  have h3 : 1 + k = k + 1 := by omega
  rw [h1, h2, h3]
  have h4 : fib (k + 2) = fib k + fib (k + 1) := fib_add_two
  omega

-- ============================================================================
-- Step 5: Cosine-Fibonacci recurrence
-- ============================================================================
lemma cos_fib_recurrence' (b : ℝ) (n : ℕ) (hn : n ≥ 2) :
    cos ((fib (n + 1) : ℕ) * b) = 2 * cos ((fib n : ℕ) * b) * cos ((fib (n - 1) : ℕ) * b)
                                  - cos ((fib (n - 2) : ℕ) * b) := by
  have h_prod := cos_prod_to_sum' ((fib n : ℕ) * b) ((fib (n - 1) : ℕ) * b)
  have h_sub_nat := fib_sub_nat' n hn
  have h_add : fib (n - 1) + fib n = fib (n + 1) := fib_add_for_rec' n (le_trans (by norm_num : 1 ≤ 2) hn)
  have h_sub_real : (fib n : ℝ) * b - (fib (n - 1) : ℝ) * b = (fib (n - 2) : ℝ) * b := by
    have h : (fib n : ℝ) - (fib (n - 1) : ℝ) = (fib (n - 2) : ℝ) := by
      rw [← Nat.cast_sub (fib_mono (Nat.sub_le n 1)), h_sub_nat]
    calc (fib n : ℝ) * b - (fib (n - 1) : ℝ) * b = ((fib n : ℝ) - (fib (n - 1) : ℝ)) * b := by ring
      _ = (fib (n - 2) : ℝ) * b := by rw [h]
  have h_add_real : (fib n : ℝ) * b + (fib (n - 1) : ℝ) * b = (fib (n + 1) : ℝ) * b := by
    have h : (fib n : ℝ) + (fib (n - 1) : ℝ) = (fib (n + 1) : ℝ) := by
      rw [add_comm, ← Nat.cast_add, h_add]
    calc (fib n : ℝ) * b + (fib (n - 1) : ℝ) * b = ((fib n : ℝ) + (fib (n - 1) : ℝ)) * b := by ring
      _ = (fib (n + 1) : ℝ) * b := by rw [h]
  rw [h_prod, h_sub_real, h_add_real]; ring

-- ============================================================================
-- Step 6: Main theorem
-- ============================================================================
theorem Putnam_exercise_2018_b4 (a : ℝ) (x : ℕ → ℝ) (hx0 : x 0 = 1)
  (hx1 : x 1 = a) (hx2 : x 2 = a)
  (hxn : ∀ n : ℕ, n ≥ 2 → x (n+1) = 2*(x n)*(x (n-1)) - x (n-2))
  (h : ∃ n, x n = 0) :
  ∃ c ≠ 0, Periodic x c := by
  /-
  Step 6.1: Case split on |a| > 1 vs |a| ≤ 1

  Step 6.2 (|a| > 1): Show |x_n| ≥ 1 for all n, contradicting x_n = 0

  Step 6.3 (|a| ≤ 1): Write a = cos(b), show x_n = cos(F_n · b)

  Step 6.4: If x_n = 0, then b = rational multiple of π

  Step 6.5: Use Pisano periodicity to conclude x is periodic
  -/
  classical
  by_cases ha : |a| ≤ 1
  · -- Step 6.3: Case |a| ≤ 1, write a = cos(b)
    have hb_exists : ∃ b, 0 ≤ b ∧ b ≤ π ∧ cos b = a := by
      use arccos a
      have h1 : -1 ≤ a := (abs_le.mp ha).1
      have h2 : a ≤ 1 := (abs_le.mp ha).2
      exact ⟨arccos_nonneg a, arccos_le_pi a, cos_arccos h1 h2⟩
    obtain ⟨b, _, _, hb_eq⟩ := hb_exists

    -- Step 6.3.1: Define y_n = cos(F_n · b)
    let y : ℕ → ℝ := fun n => cos ((fib n : ℕ) * b)

    -- Step 6.3.2: Show y satisfies same recurrence
    have hy0 : y 0 = 1 := by simp [y, fib_zero, cos_zero]
    have hy1 : y 1 = a := by simp [y, fib_one, one_mul, hb_eq]
    have hy2 : y 2 = a := by simp [y, fib_two, one_mul, hb_eq]
    have hyn : ∀ n ≥ 2, y (n + 1) = 2 * y n * y (n - 1) - y (n - 2) := by
      intro n hn; simp only [y]; exact cos_fib_recurrence' b n hn

    -- Step 6.3.3: By uniqueness, x = y
    have hxy : ∀ n, x n = y n := by
      intro n; induction n using Nat.strong_induction_on with | _ n ih =>
        match n with
        | 0 => rw [hx0, hy0]
        | 1 => rw [hx1, hy1]
        | 2 => rw [hx2, hy2]
        | k + 3 =>
          have h1 := hxn (k + 2) (by omega)
          have h2 := hyn (k + 2) (by omega)
          have h4 : k + 2 - 1 = k + 1 := by omega
          have h5 : k + 2 - 2 = k := by omega
          simp only [h4, h5] at h1 h2
          rw [h1, h2, ih (k + 2) (by omega), ih (k + 1) (by omega), ih k (by omega)]

    -- Step 6.4: Use x_n = 0 to get periodicity
    obtain ⟨n₀, hn₀⟩ := h
    rw [hxy n₀] at hn₀
    simp only [y] at hn₀

    -- Step 6.4.1: cos(F_{n₀} · b) = 0 means F_{n₀} · b = (2k+1)π/2
    have hcos_zero : ∃ k : ℤ, (fib n₀ : ℝ) * b = (2 * k + 1) * π / 2 := cos_eq_zero_iff.mp hn₀
    obtain ⟨k₀, hk₀⟩ := hcos_zero

    -- Step 6.4.2: Handle the case fib n₀ = 0
    by_cases hfib_zero : fib n₀ = 0
    · -- If F_{n₀} = 0, then n₀ = 0, but x 0 = 1 ≠ 0
      have hn0_eq : n₀ = 0 := by
        cases n₀ with
        | zero => rfl
        | succ k =>
          have : fib (k + 1) > 0 := Nat.fib_pos.mpr (by omega)
          omega
      -- n₀ = 0, so hn₀ says cos(0 * b) = 0, i.e., cos 0 = 0, contradiction
      simp only [hn0_eq, fib_zero, Nat.cast_zero, zero_mul, cos_zero] at hn₀
      exact absurd hn₀ one_ne_zero
    · -- Step 6.5: F_{n₀} > 0, use Pisano periodicity
      have hfib_pos : fib n₀ > 0 := Nat.pos_of_ne_zero hfib_zero

      -- Step 6.5.1: Get Pisano period for 4 * F_{n₀}
      have h_pisano := fib_mod_periodic' (4 * fib n₀) (by omega : 4 * fib n₀ > 0)
      obtain ⟨T, hT_pos, hT_period⟩ := h_pisano

      -- Step 6.5.2: Show x is periodic with period T
      use T
      constructor; · omega
      · intro n
        rw [hxy, hxy]
        simp only [y]

        -- Step 6.5.3: Key: F_{n+T} ≡ F_n (mod 4·F_{n₀})
        have h_mod : fib (n + T) % (4 * fib n₀) = fib n % (4 * fib n₀) := hT_period n

        -- Step 6.5.4: This means F_{n+T} - F_n = 4·F_{n₀}·q for some q
        have h_diff : ∃ q : ℤ, (fib (n + T) : ℤ) - fib n = 4 * fib n₀ * q := by
          have h1 : (fib (n + T) : ℤ) % (4 * fib n₀) = (fib n : ℤ) % (4 * fib n₀) := by
            have h_nat := h_mod
            simp only at h_nat ⊢
            exact congrArg (Int.ofNat) h_nat
          have h2 : ((fib (n + T) : ℤ) - fib n) % (4 * fib n₀) = 0 := by
            rw [Int.sub_emod, h1, Int.sub_self, Int.zero_emod]
          exact Int.dvd_iff_emod_eq_zero.mpr h2
        obtain ⟨q, hq⟩ := h_diff

        -- Step 6.5.5: Express b in terms of k₀ and F_{n₀}
        have h_b : b = (2 * k₀ + 1) * π / (2 * fib n₀) := by
          have hfn0_ne : (fib n₀ : ℝ) ≠ 0 := by simp [hfib_zero]
          field_simp at hk₀ ⊢; linarith

        -- Step 6.5.6: Compute cos(F_{n+T} · b) = cos(F_n · b)
        have hcast : ((fib (n + T) : ℕ) : ℝ) - (fib n : ℕ) = 4 * (fib n₀ : ℝ) * q := by
          -- The key is to show that the ℝ version follows from the ℤ version
          -- hq: (fib (n + T) : ℤ) - (fib n : ℤ) = 4 * (fib n₀ : ℤ) * q
          have h_int_to_real : ((fib (n + T) : ℤ) : ℝ) - ((fib n : ℤ) : ℝ) = 4 * ((fib n₀ : ℤ) : ℝ) * (q : ℝ) := by
            have := congrArg (Int.cast (R := ℝ)) hq
            simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat] at this
            convert this using 1
          simp only [Int.cast_natCast] at h_int_to_real
          exact h_int_to_real

        calc cos ((fib (n + T) : ℕ) * b)
            = cos ((fib n : ℕ) * b + ((fib (n + T) : ℕ) - (fib n : ℕ)) * b) := by ring_nf
          _ = cos ((fib n : ℕ) * b + (4 * (fib n₀ : ℝ) * q) * b) := by rw [hcast]
          _ = cos ((fib n : ℕ) * b + (4 * (fib n₀ : ℝ) * q) * ((2 * k₀ + 1) * π / (2 * fib n₀))) := by rw [h_b]
          _ = cos ((fib n : ℕ) * b + q * (2 * k₀ + 1) * 2 * π) := by
              congr 1; have hfn0_ne : (fib n₀ : ℝ) ≠ 0 := by simp [hfib_zero]
              field_simp; ring
          _ = cos ((fib n : ℕ) * b) := by
              have h := cos_add_int_mul_two_pi ((fib n : ℕ) * b) (q * (2 * k₀ + 1))
              convert h using 2
              push_cast; ring

  · -- Step 6.2: Case |a| > 1
    push_neg at ha
    -- Step 6.2.1: Show |x_n| ≥ 1 AND |x_{n+1}| ≥ |x_n| (monotonicity) by strong induction
    -- The informal proof shows: |x_{n+1}| ≥ |x_n|(2|x_{n-1}| - 1) ≥ |x_n| when |x_{n-1}| ≥ 1
    -- This gives both monotonicity and the lower bound |x_n| ≥ 1.
    have h_mono_and_bound : ∀ n, |x n| ≥ 1 ∧ (n ≥ 1 → |x n| ≥ |x (n - 1)|) := by
      intro n; induction n using Nat.strong_induction_on with | _ n ih =>
        match n with
        | 0 =>
          refine ⟨?_, ?_⟩
          · rw [hx0]; simp
          · intro habs; exact absurd habs (by decide : ¬(0 ≥ 1))
        | 1 =>
          refine ⟨?_, ?_⟩
          · rw [hx1]; exact le_of_lt ha
          · intro _
            have h11 : (1 : ℕ) - 1 = 0 := by norm_num
            rw [h11, hx1, hx0]
            simp only [abs_one]
            exact le_of_lt ha
        | 2 =>
          refine ⟨?_, ?_⟩
          · rw [hx2]; exact le_of_lt ha
          · intro _
            have h21 : (2 : ℕ) - 1 = 1 := by norm_num
            rw [h21, hx2, hx1]
        | k + 3 =>
          have ih0 := ih k (by omega)
          have ih1 := ih (k + 1) (by omega)
          have ih2 := ih (k + 2) (by omega)
          have hbound0 : |x k| ≥ 1 := ih0.1
          have hbound1 : |x (k + 1)| ≥ 1 := ih1.1
          have hbound2 : |x (k + 2)| ≥ 1 := ih2.1
          -- Get monotonicity facts
          have hmono1 : |x (k + 1)| ≥ |x k| := ih1.2 (by omega)
          have hmono2 : |x (k + 2)| ≥ |x (k + 1)| := ih2.2 (by omega)
          have h1 := hxn (k + 2) (by omega)
          have h4 : k + 2 - 1 = k + 1 := by omega
          have h5 : k + 2 - 2 = k := by omega
          simp only [h4, h5] at h1
          -- Need to show |x(k+3)| ≥ 1 and |x(k+3)| ≥ |x(k+2)|
          -- x(k+3) = 2*x(k+2)*x(k+1) - x(k)
          -- |x(k+3)| = |2*x(k+2)*x(k+1) - x(k)| ≥ 2|x(k+2)||x(k+1)| - |x(k)|  (reverse triangle)
          --          ≥ |x(k+2)|(2|x(k+1)| - 1) ≥ |x(k+2)|  (since |x(k+1)| ≥ 1)
          have h_rev_tri : |2 * x (k + 2) * x (k + 1) - x k| ≥
                           2 * |x (k + 2)| * |x (k + 1)| - |x k| := by
            have := abs_sub_abs_le_abs_sub (2 * x (k + 2) * x (k + 1)) (x k)
            have h_abs_mul : |2 * x (k + 2) * x (k + 1)| = 2 * |x (k + 2)| * |x (k + 1)| := by
              rw [abs_mul, abs_mul]
              have : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num : (2 : ℝ) > 0)
              rw [this]
            linarith
          -- Key inequality: 2|x(k+2)||x(k+1)| - |x(k)| ≥ |x(k+2)|
          -- This follows from: 2|x(k+2)||x(k+1)| ≥ |x(k+2)| + |x(k)|
          --                   2|x(k+1)| ≥ 1 + |x(k)|/|x(k+2)|
          -- Since |x(k)| ≤ |x(k+1)| ≤ |x(k+2)| (monotonicity), we have |x(k)|/|x(k+2)| ≤ 1
          -- So 2|x(k+1)| ≥ 2 ≥ 1 + 1 ≥ 1 + |x(k)|/|x(k+2)| ✓
          have hkey : 2 * |x (k + 2)| * |x (k + 1)| - |x k| ≥ |x (k + 2)| := by
            -- Using monotonicity: |x k| ≤ |x(k+1)| ≤ |x(k+2)|
            -- So 2*|x(k+2)|*|x(k+1)| ≥ 2*|x(k+1)|*|x(k+1)| ≥ 2*|x(k+1)|
            --    ≥ 2*|x k| (by monotonicity)
            -- Therefore 2*|x(k+2)|*|x(k+1)| - |x k| ≥ 2*|x k| - |x k| = |x k| ≥ 1
            -- But we need ≥ |x(k+2)|, which requires more care.
            -- Actually: 2*|x(k+2)|*|x(k+1)| - |x k| ≥ |x(k+2)| iff
            --          2*|x(k+2)|*|x(k+1)| - |x(k+2)| ≥ |x k| iff
            --          |x(k+2)|*(2|x(k+1)| - 1) ≥ |x k|
            -- Since |x(k+1)| ≥ 1, we have 2|x(k+1)| - 1 ≥ 1
            -- So |x(k+2)|*(2|x(k+1)| - 1) ≥ |x(k+2)| ≥ |x(k+1)| ≥ |x k| by monotonicity ✓
            have pos2 : |x (k + 2)| > 0 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hbound2
            have factor_ge_1 : 2 * |x (k + 1)| - 1 ≥ 1 := by linarith
            have prod_ge : |x (k + 2)| * (2 * |x (k + 1)| - 1) ≥ |x (k + 2)| := by
              have h := mul_le_mul_of_nonneg_left factor_ge_1 (le_of_lt pos2)
              simp only [mul_one] at h; exact h
            have chain : |x (k + 2)| ≥ |x k| := le_trans hmono1 hmono2
            calc 2 * |x (k + 2)| * |x (k + 1)| - |x k|
                = |x (k + 2)| * (2 * |x (k + 1)|) - |x k| := by ring
              _ = |x (k + 2)| * (2 * |x (k + 1)| - 1) + |x (k + 2)| - |x k| := by ring
              _ ≥ |x (k + 2)| + |x (k + 2)| - |x k| := by linarith [prod_ge]
              _ ≥ |x (k + 2)| + |x k| - |x k| := by linarith [chain]
              _ = |x (k + 2)| := by ring
          constructor
          · -- |x(k+3)| ≥ 1
            rw [h1]
            calc |2 * x (k + 2) * x (k + 1) - x k|
                ≥ |x (k + 2)| := le_trans hkey h_rev_tri
              _ ≥ 1 := hbound2
          · -- |x(k+3)| ≥ |x(k+2)|
            intro _
            rw [h1]
            have h6 : k + 3 - 1 = k + 2 := by omega
            rw [h6]
            exact le_trans hkey h_rev_tri
    /- h_mono_and_bound is now defined -/
    /- Step 6.2.2: Extract just the bound and derive contradiction
       We prove False from the assumption that x_n = 0 for some n
       Since the goal is ∃ c, c ≠ 0 ∧ Periodic x c, and we have a contradiction,
       we use exfalso -/
    exfalso
    obtain ⟨n₀, hn₀⟩ := h
    have h_bound : |x n₀| ≥ 1 := (h_mono_and_bound n₀).1
    rw [hn₀] at h_bound
    simp only [abs_zero] at h_bound
    exact absurd h_bound (by norm_num : ¬(1 : ℝ) ≤ 0)
