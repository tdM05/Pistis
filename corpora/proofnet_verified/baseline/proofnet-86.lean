import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

/-Informal Statement

Let $p$ be an odd prime and let $1 + \frac{1}{2} + ... + \frac{1}{p - 1} = \frac{a}{b}$, where $a, b$ are integers. Show that $p \mid a$.
-/

/-Informal Proof

First we prove for prime $p=3$ and then for all prime $p>3$.
Let us take $p=3$. Then the sum
$$
\frac{1}{1}+\frac{1}{2}+\ldots+\frac{1}{(p-1)}
$$
becomes
$$
1+\frac{1}{3-1}=1+\frac{1}{2}=\frac{3}{2} .
$$
Therefore in this case $\quad \frac{a}{b}=\frac{3}{2} \quad$ implies $3 \mid a$, i.e. $p \mid a$.
Now for odd prime $p>3$.
Let us consider $f(x)=(x-1)(x-2) \ldots(x-(p-1))$.
Now, by Fermat, we know that the coefficients of $f(x)$ other than the $x^{p-1}$ and $x^0$ are divisible by $p$.
So if,
$$
\begin{array}{r}
f(x)=x^{p-1}+\sum_{i=0}^{p-2} a_i x^i \\
\text { and } p>3 .
\end{array}
$$
Then $p \mid a_2$, and
$$
f(p) \equiv a_1 p+a_0 \quad\left(\bmod p^3\right)
$$
But we see that
$$
f(x)=(-1)^{p-1} f(p-x) \text { for any } x,
$$
so if $p$ is odd,
$$
f(p)=f(0)=a_0,
$$
So it follows that:
$$
0=f(p)-a_0 \equiv a_1 p \quad\left(\bmod p^3\right)
$$
Therefore,
$$
0 \equiv a_1 \quad\left(\bmod p^2\right) .
$$
Hence,
$$
0 \equiv a_1 \quad(\bmod p) .
$$
Now our sum is just $\frac{a_1}{(p-1) !}=\frac{a}{b}$.
It follows that $p$ divides $a$. This completes the proof.
-/

/-
Alternative proof using pairing argument (used for the formal proof):
---------------------------------------------------------------------

For an odd prime p, the sum S = 1 + 1/2 + ... + 1/(p-1) can be paired:
  1/k + 1/(p-k) = p/(k(p-k)) for k = 1, ..., (p-1)/2

So S = ∑_{k=1}^{(p-1)/2} p/(k(p-k)) = p * T
where T = ∑_{k=1}^{(p-1)/2} 1/(k(p-k))

Since gcd(p, k(p-k)) = 1 for all k ∈ {1,...,p-1} (as p is prime and k, p-k < p),
we have gcd(p, T.den) = 1. Therefore p | S.num.

For any a/b = S, since S.num is divisible by p and gcd(S.num, S.den) = 1,
we can show a = S.num * c for some c, hence p | a.
-/

-- Step 1: Lemma establishing the pairing identity 1/k + 1/(p-k) = p/(k(p-k))
lemma pairing_identity' {p k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < p) :
    (1 : ℚ) / k + 1 / ((p : ℚ) - k) = p / (k * ((p : ℚ) - k)) := by
  -- Step 1.1: Establish that k and p-k are non-zero in ℚ
  have hk_lt_p : (k : ℚ) < p := Nat.cast_lt.mpr hk2
  have hk_ne : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpmk_ne : (p : ℚ) - k ≠ 0 := by linarith
  -- Step 1.2: Clear denominators and verify algebraically
  field_simp [hk_ne, hpmk_ne]
  ring

-- Step 2: Key number-theoretic lemma: When gcd(p, q.den) = 1, p divides (p * q).num
-- This shows that multiplying by p preserves divisibility by p when the denominator is coprime to p
lemma p_dvd_p_mul_num {p : ℕ} (q : ℚ) (_hp : Nat.Prime p) (hcop : Nat.Coprime p q.den) :
    (p : ℤ) ∣ ((p : ℚ) * q).num := by
  /-
  Proof outline:
  (p * q).num = (p * q.num) / gcd(|p * q.num|, q.den)

  Let g = gcd(|p * q.num|, q.den). Then:
  - g | q.den, so gcd(p, g) = 1 (since gcd(p, q.den) = 1)
  - p * q.num = g * m for some integer m
  - (p * q).num = m

  Since p | g * m and gcd(p, g) = 1, we have p | m = (p * q).num.
  -/
  -- Step 2.1: Express (p * q).num using Rat.mul_num
  have hp_num : (p : ℚ).num = p := Rat.num_natCast p
  have hp_den : (p : ℚ).den = 1 := Rat.den_natCast p

  -- Step 2.2: Compute the formula
  rw [Rat.mul_num, hp_num, hp_den, one_mul]

  -- Now goal: (p : ℤ) ∣ (p * q.num) / gcd(|p * q.num|, q.den)
  set g := (p * q.num).natAbs.gcd q.den with hg_def

  -- Step 2.3: Show p | (p * q.num)
  have hp_dvd_pq : (p : ℤ) ∣ p * q.num := dvd_mul_right (p : ℤ) q.num

  -- Step 2.4: Show gcd(p, g) = 1
  have hg_dvd_den : g ∣ q.den := Nat.gcd_dvd_right _ _
  have hcop_g : Nat.Coprime p g := Nat.Coprime.coprime_dvd_right hg_dvd_den hcop

  -- Step 2.5: g | (p * q.num).natAbs
  have hg_dvd : g ∣ (p * q.num).natAbs := Nat.gcd_dvd_left _ _

  -- Step 2.6: Convert to integer divisibility: (g : ℤ) | (p * q.num)
  have hg_dvd_int : (g : ℤ) ∣ p * q.num := by
    rw [Int.natCast_dvd]
    exact hg_dvd

  -- Step 2.7: Write p * q.num = g * m for some m
  obtain ⟨m, hm⟩ := hg_dvd_int

  -- Step 2.8: (p * q.num) / g = m
  have hg_pos : 0 < g := by
    apply Nat.gcd_pos_of_pos_right
    exact q.den_pos
  have hg_ne_zero : (g : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hg_pos)

  have hdiv_eq : (p * q.num) / (g : ℤ) = m := by
    rw [hm, Int.mul_ediv_cancel_left _ hg_ne_zero]

  rw [hdiv_eq]

  -- Step 2.9: Show p | m using Euclid's lemma
  -- We have p * q.num = g * m, so p | g * m
  -- Since gcd(p, g) = 1, we have p | m
  have hp_dvd_gm : (p : ℤ) ∣ g * m := by rw [← hm]; exact hp_dvd_pq

  have hcop_int : IsCoprime (p : ℤ) (g : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simp only [Int.gcd_natCast_natCast]
    exact hcop_g

  rw [mul_comm] at hp_dvd_gm
  exact hcop_int.dvd_of_dvd_mul_right hp_dvd_gm

-- Step 3: Lemma showing that a sum of fractions with denominators coprime to p
-- has a denominator that is also coprime to p
lemma sum_den_coprime_of_terms_coprime {s : Finset ℕ} {f : ℕ → ℚ}
    {p : ℕ} (_hp : Nat.Prime p) (hcop : ∀ i ∈ s, Nat.Coprime p (f i).den) :
    Nat.Coprime p (∑ i ∈ s, f i).den := by
  -- Step 3.1: Induction on the size of s
  induction s using Finset.induction_on with
  | empty =>
    -- Step 3.2: Base case: empty sum has denominator 1, which is coprime to p
    simp only [Finset.sum_empty, Rat.den_zero]
    exact Nat.coprime_one_right p
  | insert a s ha ih =>
    -- Step 3.3: Inductive case: use Rat.add_den_dvd and coprimality of product
    simp only [Finset.sum_insert ha]
    have hcop_a : Nat.Coprime p (f a).den := hcop a (Finset.mem_insert_self a s)
    have hcop_s : ∀ i ∈ s, Nat.Coprime p (f i).den := fun i hi =>
      hcop i (Finset.mem_insert_of_mem hi)
    have hcop_sum : Nat.Coprime p (∑ i ∈ s, f i).den := ih hcop_s

    -- Step 3.4: The denominator of a sum divides the product of individual denominators
    have hden_dvd : (f a + ∑ i ∈ s, f i).den ∣ (f a).den * (∑ i ∈ s, f i).den :=
      Rat.add_den_dvd (f a) (∑ i ∈ s, f i)

    -- Step 3.5: The product is coprime to p, so the denominator is too
    have hprod_cop : Nat.Coprime p ((f a).den * (∑ i ∈ s, f i).den) :=
      Nat.Coprime.mul_right hcop_a hcop_sum

    exact Nat.Coprime.coprime_dvd_right hden_dvd hprod_cop

-- Step 4: The main pairing lemma showing S = p * T
lemma harmonic_pairing {p : ℕ} (hp : Nat.Prime p) (hp_odd : Odd p) :
    ∑ i ∈ Finset.range (p-1), (1 / ((i : ℚ) + 1)) =
    (p : ℚ) * ∑ k ∈ Finset.Icc 1 ((p-1)/2), (1 / ((k : ℚ) * ((p : ℚ) - k))) := by
  -- Step 4.1: Establish basic facts
  have hp3 : 3 ≤ p := by
    rcases hp_odd with ⟨m, hm⟩
    have hp2 := hp.two_le
    omega
  have hp_pos : 0 < p := by omega

  -- Step 4.2: Get the odd form p = 2m + 1, so (p-1)/2 = m
  obtain ⟨m, hm⟩ := hp_odd
  have hm_eq : (p - 1) / 2 = m := by omega

  -- Step 4.3: Rewrite the LHS as a sum over Icc 1 (p-1) instead of range (p-1)
  have hLHS_eq : ∑ i ∈ Finset.range (p-1), (1 / ((i : ℚ) + 1)) =
                 ∑ k ∈ Finset.Icc 1 (p-1), (1 / (k : ℚ)) := by
    -- Bijection: i ↦ i + 1 from range (p-1) to Icc 1 (p-1)
    refine Finset.sum_bij' (fun i _ => i + 1) (fun k _ => k - 1) ?hi ?hj ?left_inv ?right_inv ?heq
    case hi =>
      intro i hi
      have hi' : i < p - 1 := Finset.mem_range.mp hi
      have h1 : 1 ≤ i + 1 := Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero i)
      have h2 : i + 1 ≤ p - 1 := Nat.succ_le_of_lt hi'
      exact Finset.mem_Icc.mpr ⟨h1, h2⟩
    case hj =>
      intro k hk
      have ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
      have h : k - 1 < p - 1 := by
        calc k - 1 < k := Nat.sub_lt (by linarith) (by linarith)
          _ ≤ p - 1 := hk2
      exact Finset.mem_range.mpr h
    case left_inv =>
      intro i _
      exact Nat.add_sub_cancel i 1
    case right_inv =>
      intro k hk
      have ⟨hk1, _⟩ := Finset.mem_Icc.mp hk
      exact Nat.sub_add_cancel hk1
    case heq =>
      intro i _
      simp only [Nat.cast_add, Nat.cast_one]

  rw [hLHS_eq]

  -- Step 4.4: Split Icc 1 (p-1) = Icc 1 m ∪ Icc (m+1) (2m)
  have hp_minus_1 : p - 1 = 2 * m := by omega

  have hIcc_split : Finset.Icc 1 (p - 1) = Finset.Icc 1 m ∪ Finset.Icc (m + 1) (2 * m) := by
    rw [hp_minus_1]
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc]
    constructor
    · intro ⟨h1, h2⟩
      by_cases hxm : x ≤ m
      · left; exact ⟨h1, hxm⟩
      · right; push_neg at hxm; exact ⟨hxm, h2⟩
    · intro h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1, by linarith⟩
      · exact ⟨by linarith, h2⟩

  have hIcc_disj : Disjoint (Finset.Icc 1 m) (Finset.Icc (m + 1) (2 * m)) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb heq
    have ⟨_, ha2⟩ := Finset.mem_Icc.mp ha
    have ⟨hb1, _⟩ := Finset.mem_Icc.mp hb
    subst heq
    linarith

  rw [hIcc_split, Finset.sum_union hIcc_disj]

  -- Step 4.5: Reindex the second sum using j ↦ p - j
  have hSecond_reindex :
      ∑ j ∈ Finset.Icc (m + 1) (2 * m), (1 / (j : ℚ)) =
      ∑ k ∈ Finset.Icc 1 m, (1 / ((p : ℚ) - k)) := by
    refine Finset.sum_bij' (fun j _ => p - j) (fun k _ => p - k) ?hi ?hj ?left_inv ?right_inv ?heq
    case hi =>
      intro j hj
      have ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
      have h1 : 1 ≤ p - j := by
        have hj_lt_p : j < p := by linarith
        have : 0 < p - j := Nat.sub_pos_of_lt hj_lt_p
        exact this
      have h2 : p - j ≤ m := by
        have hp1 : p = 2 * m + 1 := hm
        calc p - j ≤ p - (m + 1) := Nat.sub_le_sub_left hj1 p
          _ = 2 * m + 1 - (m + 1) := by rw [hp1]
          _ = m := by omega
      exact Finset.mem_Icc.mpr ⟨h1, h2⟩
    case hj =>
      intro k hk
      have ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
      have hp1 : p = 2 * m + 1 := hm
      have h1 : m + 1 ≤ p - k := by
        calc m + 1 = p - m := by omega
          _ ≤ p - k := Nat.sub_le_sub_left hk2 p
      have h2 : p - k ≤ 2 * m := by
        calc p - k ≤ p - 1 := Nat.sub_le_sub_left hk1 p
          _ = 2 * m := hp_minus_1
      exact Finset.mem_Icc.mpr ⟨h1, h2⟩
    case left_inv =>
      intro j hj
      have ⟨_, hj2⟩ := Finset.mem_Icc.mp hj
      have hj_le_p : j ≤ p := by linarith
      exact Nat.sub_sub_self hj_le_p
    case right_inv =>
      intro k hk
      have ⟨_, hk2⟩ := Finset.mem_Icc.mp hk
      have hk_le_p : k ≤ p := by linarith
      exact Nat.sub_sub_self hk_le_p
    case heq =>
      intro j hj
      have ⟨_, hj2⟩ := Finset.mem_Icc.mp hj
      have hj_le_p : j ≤ p := by linarith
      have hpmj_le_p : p - j ≤ p := Nat.sub_le p j
      congr 1
      have h1 : p - (p - j) = j := Nat.sub_sub_self hj_le_p
      have h2 : (p : ℚ) - ((p - j : ℕ) : ℚ) = ((p - (p - j) : ℕ) : ℚ) := by
        rw [← Nat.cast_sub hpmj_le_p]
      rw [h2, h1]

  rw [hSecond_reindex]

  -- Step 4.6: Combine: ∑_{k∈Icc 1 m} (1/k + 1/(p-k))
  rw [← Finset.sum_add_distrib]

  -- Step 4.7: Apply the pairing identity
  have hPairing : ∀ k ∈ Finset.Icc 1 m, (1 : ℚ) / k + 1 / ((p : ℚ) - k) =
                  (p : ℚ) / (k * ((p : ℚ) - k)) := by
    intro k hk
    have ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    have hk_lt : k < p := by linarith
    exact pairing_identity' hk1 hk_lt

  have hSum_eq : ∑ k ∈ Finset.Icc 1 m, (1 / (k : ℚ) + 1 / ((p : ℚ) - k)) =
                 ∑ k ∈ Finset.Icc 1 m, (p : ℚ) / ((k : ℚ) * ((p : ℚ) - k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hPairing k hk

  rw [hSum_eq]

  -- Step 4.8: Factor out p
  have hFactor : ∑ k ∈ Finset.Icc 1 m, (p : ℚ) / ((k : ℚ) * ((p : ℚ) - k)) =
                 (p : ℚ) * ∑ k ∈ Finset.Icc 1 m, 1 / ((k : ℚ) * ((p : ℚ) - k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    have hk_ne : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by linarith : k ≠ 0)
    have hpmk_pos : 0 < p - k := by
      have hk_lt : k < p := by linarith
      exact Nat.sub_pos_of_lt hk_lt
    have hpmk_ne : (p : ℚ) - k ≠ 0 := by
      have hk_le : k ≤ p := by linarith
      have h : (0 : ℚ) < p - k := by
        calc (0 : ℚ) < ((p - k : ℕ) : ℚ) := Nat.cast_pos.mpr hpmk_pos
          _ = (p : ℚ) - k := by rw [Nat.cast_sub hk_le]
      linarith
    field_simp [hk_ne, hpmk_ne]

  rw [hFactor]

  -- Step 4.9: The ranges are equal since (p-1)/2 = m
  congr 1
  rw [hm_eq]

-- Step 5: Key lemma that p divides the numerator of the harmonic sum (in lowest terms)
-- This follows from the pairing argument showing S = p * T with gcd(p, T.den) = 1
lemma p_dvd_harmonic_num {p : ℕ} (hp : Nat.Prime p) (hp1 : Odd p) :
    (p : ℤ) ∣ (∑ i ∈ Finset.range (p-1), (1 / (i + 1) : ℚ)).num := by
  -- Step 5.1: Establish p ≥ 3 (since p is an odd prime)
  have hp3 : 3 ≤ p := by rcases hp1 with ⟨k, hk⟩; have hp2 := hp.two_le; omega

  -- Step 5.2: Define the sum S = 1 + 1/2 + ... + 1/(p-1)
  set S : ℚ := ∑ i ∈ Finset.range (p-1), (1 / (i + 1) : ℚ) with hS_def

  -- Step 5.3: Define T = ∑_{k=1}^{(p-1)/2} 1/(k * (p - k))
  let T : ℚ := ∑ k ∈ Finset.Icc 1 ((p-1)/2), (1 / ((k : ℚ) * ((p : ℚ) - k)))

  -- Step 5.4: Show S = p * T using the pairing argument
  have hST : S = p * T := harmonic_pairing hp hp1

  -- Step 5.5: Show gcd(p, T.den) = 1
  have hcoprime : Nat.Coprime p T.den := by
    -- Step 5.5.1: Each term 1/(k(p-k)) has denominator coprime to p
    have hterms_cop : ∀ k ∈ Finset.Icc 1 ((p-1)/2),
        Nat.Coprime p ((fun k => (1 : ℚ) / ((k : ℚ) * ((p : ℚ) - k))) k).den := by
      intro k hk
      simp only [Finset.mem_Icc] at hk
      have hp_pos : 0 < p := by omega
      have hk_lt : k < p := by
        have h2 : (p - 1) / 2 < p := by
          have hsub_pos : 0 < p - 1 := Nat.sub_pos_of_lt (Nat.Prime.one_lt hp)
          calc (p - 1) / 2 < p - 1 := Nat.div_lt_self hsub_pos (by omega)
            _ < p := Nat.sub_lt hp_pos (by omega)
        omega
      have hpmk_pos : 0 < p - k := Nat.sub_pos_of_lt hk_lt
      have hpmk_lt : p - k < p := Nat.sub_lt hp_pos (by omega)

      -- Step 5.5.2: k * (p - k) as a natural number equals the ℚ product
      have heq_nat : (k : ℚ) * ((p : ℚ) - k) = ((k * (p - k) : ℕ) : ℚ) := by
        have hle : k ≤ p := le_of_lt hk_lt
        simp only [Nat.cast_mul, Nat.cast_sub hle]

      simp only [heq_nat]

      -- Step 5.5.3: For 1/(n : ℚ) where n : ℕ > 0, the denominator is n
      have hprod_pos : 0 < k * (p - k) := Nat.mul_pos (by omega) hpmk_pos
      have hden_eq : (1 / ((k * (p - k) : ℕ) : ℚ)).den = k * (p - k) := by
        rw [one_div, Rat.inv_natCast_den]
        simp only [ite_eq_right_iff]
        intro h
        exact absurd h (Nat.pos_iff_ne_zero.mp hprod_pos)

      rw [hden_eq]

      -- Step 5.5.4: k * (p - k) is coprime to p since k < p and p - k < p
      apply Nat.Coprime.mul_right
      · exact (Nat.Prime.coprime_iff_not_dvd hp).mpr
          (fun h => Nat.not_lt.mpr (Nat.le_of_dvd (by omega) h) hk_lt)
      · exact (Nat.Prime.coprime_iff_not_dvd hp).mpr
          (fun h => Nat.not_lt.mpr (Nat.le_of_dvd hpmk_pos h) hpmk_lt)

    -- Step 5.5.5: Apply the sum lemma
    exact sum_den_coprime_of_terms_coprime hp hterms_cop

  -- Step 5.6: Conclude p | S.num from S = p * T and gcd(p, T.den) = 1
  rw [hST]
  exact p_dvd_p_mul_num T hp hcoprime

-- Step 6: Main theorem
theorem Herstein_exercise_4_2_9 {p : ℕ} (hp : Nat.Prime p) (hp1 : Odd p) :
  ∀ (a b : ℤ), (a / b : ℚ) = ∑ i ∈ Finset.range (p-1), (1 / (i + 1) : ℚ) → ↑p ∣ a := by
  intro a b hab

  -- Step 6.1: Establish p ≥ 3 (since p is an odd prime)
  have hp3 : 3 ≤ p := by rcases hp1 with ⟨k, hk⟩; have hp2 := hp.two_le; omega

  -- Step 6.2: Define the sum S = 1 + 1/2 + ... + 1/(p-1)
  set S : ℚ := ∑ i ∈ Finset.range (p-1), (1 / (i + 1) : ℚ) with hS_def

  -- Step 6.3: Handle the trivial case b = 0
  -- If b = 0, then a/0 = 0 in ℚ, but S > 0 for p ≥ 3, contradiction
  by_cases hb : b = 0
  · -- Step 6.3.1: Show S > 0
    simp only [hb, Int.cast_zero, div_zero] at hab
    have hS_pos : 0 < S := by
      rw [hS_def]; apply Finset.sum_pos
      · intro i _; exact div_pos one_pos (by positivity)
      · simp only [Finset.nonempty_range_iff]; omega
    -- Step 6.3.2: Contradiction since 0 < S but hab says S = 0
    linarith

  -- Step 6.4: Use the key lemma that p | S.num
  have hp_dvd_Snum : (p : ℤ) ∣ S.num := p_dvd_harmonic_num hp hp1

  -- Step 6.5: From p | S.num and a/b = S, conclude p | a
  -- Step 6.5.1: Handle the trivial case a = 0
  by_cases ha : a = 0
  · simp [ha]

  -- Step 6.5.2: From a/b = S, derive a = S * b
  have hb_ne : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb
  have hab' : (a : ℚ) = S * b := by field_simp [hb_ne] at hab ⊢; linarith

  -- Step 6.5.3: S = S.num / S.den in lowest terms
  have hS_eq : S = S.num / S.den := (Rat.num_div_den S).symm

  -- Step 6.5.4: From a/b = S, we have a * S.den = S.num * b
  -- Since gcd(S.num, S.den) = 1, we have S.den | b
  have hden_dvd_b : (S.den : ℤ) ∣ b := by
    -- Step 6.5.4.1: Derive a * S.den = S.num * b
    have h1 : (a : ℚ) = (S.num : ℚ) / S.den * b := by rw [← hS_eq, hab']
    have h2 : (a : ℚ) * S.den = S.num * b := by field_simp [Rat.den_ne_zero S] at h1; linarith
    have h3 : (a * S.den : ℤ) = S.num * b := by push_cast at h2; exact_mod_cast h2
    -- Step 6.5.4.2: S.den | S.num * b
    have hdvd : (S.den : ℤ) ∣ S.num * b := ⟨a, by linarith⟩
    -- Step 6.5.4.3: gcd(S.num, S.den) = 1, so IsCoprime S.num S.den
    have hcop : IsCoprime S.num (S.den : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]; exact S.reduced
    -- Step 6.5.4.4: By coprimality, S.den | b
    exact IsCoprime.dvd_of_dvd_mul_left hcop.symm hdvd

  -- Step 6.5.5: So b = S.den * c for some integer c
  obtain ⟨c, hc⟩ := hden_dvd_b

  -- Step 6.5.6: From a = S * b = (S.num / S.den) * (S.den * c) = S.num * c
  have ha_eq : a = S.num * c := by
    have h1 : (a : ℚ) = S * b := hab'
    rw [hS_eq, hc] at h1
    simp only [Int.cast_mul, Int.cast_natCast] at h1
    field_simp [Rat.den_ne_zero S] at h1
    exact_mod_cast (h1 : (a : ℚ) = S.num * c)

  -- Step 6.5.7: Since p | S.num, we have p | S.num * c = a
  rw [ha_eq]
  exact dvd_mul_of_dvd_left hp_dvd_Snum c
