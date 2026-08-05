import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Show that if $G=\langle x\rangle$ is a cyclic group of order $n \geq 1$ then a subgroup $H$ is maximal if and only $H=\left\langle x^{p}\right\rangle$ for some prime $p$ dividing $n$.
-/

/-Informal Proof

Suppose $H$ is a maximal subgroup of $G$. Then $H$ is cyclic, and we may write $H=\left\langle x^k\right\rangle$ for some integer $k$, with $k>1$. Let $d=(n, k)$. Since $H$ is a proper subgroup, we know by Proposition 6 that $d>1$. Choose a prime factor $p$ of $d$. If $k=p=d$ then $k \mid n$ as required.

If, however, $k$ is not prime, then consider the subgroup $K=\left\langle x^p\right\rangle$. Since $p$ is a proper divisor of $k$, it follows that $H<K$. But $H$ is maximal, so we must have $K=G$. Again by Proposition 6 , we must then have $(p, n)=1$. However, $p$ divides $d$ which divides $n$, so $p \mid n$ and $(p, n)=p>1$, a contradiction. Therefore $k=p$ and the left-to-right implication holds.
Now, for the converse, suppose $H=\left\langle x^p\right\rangle$ for $p$ a prime dividing $n$. If $H$ is not maximal then the first part of this exercise shows that there is a maximal subgroup $K$ containing $H$. Then $K=\left\langle x^q\right\rangle$. So $x^p \in\left\langle x^q\right\rangle$, which implies $q \mid p$. But the only divisors of $p$ are 1 and $p$. If $q=1$ then $K=G$ and $K$ cannot be a proper subgroup, and if $q=p$ then $H=K$ and $H$ cannot be a proper subgroup of $K$. This contradiction shows that $H$ is maximal.
-/

/-
  ============================================================================
  STEP 0: Helper lemmas for modular arithmetic and zpowers membership
  ============================================================================
-/

-- Step 0.1: Key equivalence - (x^b)^k = x^a iff b*k ≡ a (mod orderOf x)
-- This translates zpow equality to modular arithmetic
lemma pow_zpow_eq_pow_iff {G : Type*} [Group G] (x : G) (a b : ℕ) (k : ℤ) :
    (x ^ b) ^ k = x ^ a ↔ (b : ℤ) * k ≡ (a : ℤ) [ZMOD (orderOf x : ℤ)] := by
  -- Step 0.1.1: Rewrite x^b as zpow
  rw [← zpow_natCast x b, ← zpow_mul, ← zpow_natCast x a]
  -- Step 0.1.2: Apply the zpow modular equivalence
  exact zpow_eq_zpow_iff_modEq

-- Step 0.2: Linear congruence solvability - gcd(n,b) | a implies ∃ k, b*k ≡ a (mod n)
-- This is the sufficient condition for the linear congruence b*k ≡ a (mod n)
lemma exists_mul_modEq_of_gcd_dvd {n a b : ℕ} (h : n.gcd b ∣ a) :
    ∃ k : ℤ, (b : ℤ) * k ≡ (a : ℤ) [ZMOD (n : ℤ)] := by
  -- Step 0.2.1: Write a = gcd * q for some q
  obtain ⟨q, hq⟩ := h
  -- Step 0.2.2: Use k = gcdB * q as the solution (from Bezout's identity)
  use n.gcdB b * q
  rw [hq]
  -- Step 0.2.3: Get Bezout's identity: n * gcdA + b * gcdB = gcd
  have hbezout := Nat.gcd_eq_gcd_ab n b
  rw [Int.ModEq]
  -- Step 0.2.4: Derive b * gcdB = gcd - n * gcdA
  have h1 : (b : ℤ) * n.gcdB b = (n.gcd b : ℤ) - (n : ℤ) * n.gcdA b := by
    have : (n.gcd b : ℤ) = (n : ℤ) * n.gcdA b + (b : ℤ) * n.gcdB b := hbezout
    linarith
  -- Step 0.2.5: Show the modular equality by calculation
  calc ((b : ℤ) * (n.gcdB b * q)) % n
      = ((b : ℤ) * n.gcdB b * q) % n := by ring_nf
    _ = (((n.gcd b : ℤ) - (n : ℤ) * n.gcdA b) * q) % n := by rw [h1]
    _ = ((n.gcd b : ℤ) * q - (n : ℤ) * n.gcdA b * q) % n := by ring_nf
    _ = ((n.gcd b : ℤ) * q) % n := by
        -- Step 0.2.5.1: n * gcdA * q ≡ 0 (mod n)
        have hmod : ((n : ℤ) * n.gcdA b * q) % (n : ℤ) = 0 := by
          have : (n : ℤ) * n.gcdA b * q = (n : ℤ) * (n.gcdA b * q) := by ring
          rw [this]
          exact Int.mul_emod_right (n : ℤ) (n.gcdA b * q)
        rw [Int.sub_emod, hmod, sub_zero, Int.emod_emod_of_dvd]
        exact dvd_refl _
    _ = (↑(n.gcd b) * ↑q) % ↑n := by norm_cast

-- Step 0.3: Linear congruence necessity - ∃ k, b*k ≡ a (mod n) implies gcd(n,b) | a
-- This is the necessary condition for the linear congruence b*k ≡ a (mod n)
lemma gcd_dvd_of_exists_mul_modEq {n a b : ℕ}
    (h : ∃ k : ℤ, (b : ℤ) * k ≡ (a : ℤ) [ZMOD (n : ℤ)]) : n.gcd b ∣ a := by
  -- Step 0.3.1: Get the witness k
  obtain ⟨k, hk⟩ := h
  rw [Int.ModEq] at hk
  -- Step 0.3.2: Establish divisibility facts
  have hdvd_n : (n.gcd b : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left n b)
  have hdvd_b : (n.gcd b : ℤ) ∣ (b : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right n b)
  have hdvd_bk : (n.gcd b : ℤ) ∣ (b : ℤ) * k := dvd_mul_of_dvd_left hdvd_b k
  -- Step 0.3.3: n | (b*k - a) from the modular equality
  have hdiff : (n : ℤ) ∣ ((b : ℤ) * k - (a : ℤ)) := by
    rw [Int.dvd_iff_emod_eq_zero, Int.sub_emod, hk, sub_self]
    simp only [Int.zero_emod]
  -- Step 0.3.4: gcd | (b*k - a) since gcd | n
  have hgcd_dvd_diff : (n.gcd b : ℤ) ∣ ((b : ℤ) * k - (a : ℤ)) := dvd_trans hdvd_n hdiff
  -- Step 0.3.5: gcd | a since gcd | b*k and gcd | (b*k - a)
  have : (n.gcd b : ℤ) ∣ ((b : ℤ) * k - ((b : ℤ) * k - (a : ℤ))) := dvd_sub hdvd_bk hgcd_dvd_diff
  simp only [sub_sub_cancel] at this
  exact Int.natCast_dvd_natCast.mp this

-- Step 0.4: Membership characterization - x^a ∈ zpowers(x^b) iff gcd(orderOf x, b) | a
-- This is the key characterization of membership in powers of cyclic generators
lemma mem_zpowers_pow_iff' {G : Type*} [Group G] (x : G) (a b : ℕ) :
    x ^ a ∈ zpowers (x ^ b) ↔ (orderOf x).gcd b ∣ a := by
  rw [mem_zpowers_iff]
  constructor
  -- Step 0.4.1: (⇒) If x^a ∈ zpowers(x^b), then gcd | a
  · intro ⟨k, hk⟩
    rw [pow_zpow_eq_pow_iff] at hk
    exact gcd_dvd_of_exists_mul_modEq ⟨k, hk⟩
  -- Step 0.4.2: (⇐) If gcd | a, then x^a ∈ zpowers(x^b)
  · intro h
    obtain ⟨k, hk⟩ := exists_mul_modEq_of_gcd_dvd h
    exact ⟨k, (pow_zpow_eq_pow_iff x a b k).mpr hk⟩

-- Step 0.5: Helper - gcd(m, gcd(m, n)) = gcd(m, n)
lemma gcd_gcd_self {m n : ℕ} : m.gcd (m.gcd n) = m.gcd n := by
  exact Nat.gcd_eq_right (Nat.gcd_dvd_left m n)

-- Step 0.6: Gcd membership - x^(gcd(n,k)) ∈ zpowers(x^k)
-- Uses Bezout's identity to construct the witness
lemma mem_zpowers_gcd {G : Type*} [Group G] (x : G) (k : ℕ) :
    x ^ (orderOf x).gcd k ∈ zpowers (x ^ k) := by
  rw [mem_zpowers_iff]
  -- Step 0.6.1: Use gcdB as the witness (from Bezout)
  use (orderOf x).gcdB k
  rw [← zpow_natCast x k, ← zpow_mul, ← zpow_natCast x ((orderOf x).gcd k)]
  rw [zpow_eq_zpow_iff_modEq]
  rw [Int.ModEq]
  -- Step 0.6.2: Get Bezout's identity
  have hbez := Nat.gcd_eq_gcd_ab (orderOf x) k
  -- Step 0.6.3: Derive k * gcdB = gcd - orderOf x * gcdA
  have h1 : (k : ℤ) * (orderOf x).gcdB k =
      ((orderOf x).gcd k : ℤ) - (orderOf x : ℤ) * (orderOf x).gcdA k := by
    have : ((orderOf x).gcd k : ℤ) =
        (orderOf x : ℤ) * (orderOf x).gcdA k + (k : ℤ) * (orderOf x).gcdB k := hbez
    linarith
  -- Step 0.6.4: Verify the modular equality
  calc ((k : ℤ) * (orderOf x).gcdB k) % (orderOf x)
      = (((orderOf x).gcd k : ℤ) - (orderOf x : ℤ) * (orderOf x).gcdA k) % (orderOf x) := by
        rw [h1]
    _ = ((orderOf x).gcd k : ℤ) % (orderOf x) := by
        have hmod : ((orderOf x : ℤ) * (orderOf x).gcdA k) % (orderOf x : ℤ) = 0 := by
          exact Int.mul_emod_right (orderOf x : ℤ) ((orderOf x).gcdA k)
        rw [Int.sub_emod, hmod, sub_zero, Int.emod_emod_of_dvd]
        exact dvd_refl _
    _ = ↑((orderOf x).gcd k) % ↑(orderOf x) := by norm_cast

-- Step 0.7: zpowers inclusion - zpowers(x^k) ≤ zpowers(x^gcd(orderOf x, k))
lemma zpowers_pow_le_zpowers_gcd {G : Type*} [Group G] (x : G) (k : ℕ) :
    zpowers (x ^ k) ≤ zpowers (x ^ (orderOf x).gcd k) := by
  rw [zpowers_le, mem_zpowers_pow_iff']
  rw [gcd_gcd_self]
  exact Nat.gcd_dvd_right (orderOf x) k

-- Step 0.8: Reverse inclusion - zpowers(x^gcd(orderOf x, k)) ≤ zpowers(x^k)
lemma zpowers_gcd_le_zpowers_pow {G : Type*} [Group G] (x : G) (k : ℕ) :
    zpowers (x ^ (orderOf x).gcd k) ≤ zpowers (x ^ k) := by
  rw [zpowers_le]
  exact mem_zpowers_gcd x k

-- Step 0.9: zpowers equality - zpowers(x^k) = zpowers(x^gcd(orderOf x, k))
-- This is the key normalization: any power generates the same subgroup as the gcd power
lemma zpowers_pow_eq_zpowers_gcd {G : Type*} [Group G] (x : G) (k : ℕ) :
    zpowers (x ^ k) = zpowers (x ^ (orderOf x).gcd k) := by
  exact le_antisymm (zpowers_pow_le_zpowers_gcd x k) (zpowers_gcd_le_zpowers_pow x k)

-- Step 0.10: zpowers of zpow equals zpowers of pow of natAbs
-- This handles the conversion between integer and natural powers
lemma zpowers_zpow_eq_zpowers_natAbs {G : Type*} [Group G] (x : G) (m : ℤ) :
    zpowers (x ^ m) = zpowers (x ^ m.natAbs) := by
  cases' Int.natAbs_eq m with habs habs
  -- Case 1: m = |m|, so x^m = x^|m|
  · conv_lhs => rw [habs, zpow_natCast]
  -- Case 2: m = -|m|, so x^m = x^(-|m|) = (x^|m|)^(-1)
  · conv_lhs => rw [habs, zpow_neg, zpow_natCast]
    -- zpowers((x^|m|)⁻¹) = zpowers(x^|m|) since inverse generates the same subgroup
    rw [zpowers_inv]

/-
  ============================================================================
  STEP 1: Handle the type equality hypothesis
  ============================================================================
  We assume `G = ⟨x⟩`, i.e. the subgroup closure of `{x}` is `⊤`.
-/

lemma closure_eq_top_of_type_eq {G : Type*} [Group G] {x : G}
    (hG : closure ({x} : Set G) = ⊤) : closure ({x} : Set G) = ⊤ := by
  simpa using hG


/-
  ============================================================================
  MAIN THEOREM
  ============================================================================
-/

theorem Dummit_Foote_exercise_2_4_16c {n : ℕ+} {G : Type*} [Group G] {x : G}
  (hx : orderOf x = n) (hG : closure ({x} : Set G) = ⊤) (H : Subgroup G) :
  (∃ p : ℕ, Prime p ∧ p ∣ n ∧ H = Subgroup.closure {x ^ p}) ↔
  (H ≠ ⊤ ∧ ∀ K : Subgroup G, H ≤ K → K = H ∨ K = ⊤) := by
  -- Step 2.0: Establish basic facts
  have hn_pos : 0 < (n : ℕ) := n.2
  -- Step 2.0.1: closure {x} = ⊤ from the type equality
  have hclosure_top : closure ({x} : Set G) = ⊤ := closure_eq_top_of_type_eq hG
  -- Step 2.0.2: G is cyclic
  haveI hcyclic : IsCyclic G := by
    rw [isCyclic_iff_exists_zpowers_eq_top]
    use x
    rw [zpowers_eq_closure, hclosure_top]

  constructor
  /-
    ============================================================================
    STEP 3: (⇒) If H = closure {x^p} for prime p | n, then H is maximal
    ============================================================================
  -/
  · intro ⟨p, hp_prime, hp_dvd, hH⟩
    constructor
    -- Step 3.1: H ≠ ⊤ (closure {x^p} is a proper subgroup)
    · intro hH_top
      -- Step 3.1.1: Rewrite H = ⊤ as zpowers(x^p) = ⊤
      rw [hH] at hH_top
      -- Step 3.1.2: closure(x^p) = ⊤ means x ∈ zpowers(x^p)
      rw [eq_top_iff, ← hclosure_top, ← zpowers_eq_closure, ← zpowers_eq_closure,
          zpowers_le] at hH_top
      -- Step 3.1.3: x ∈ zpowers(x^p) means x^1 ∈ zpowers(x^p), so gcd(n, p) | 1
      have hmem : x ^ 1 ∈ zpowers (x ^ p) := by simp only [pow_one]; exact hH_top
      rw [mem_zpowers_pow_iff', hx] at hmem
      -- Step 3.1.4: Since p | n, gcd(n, p) = p, so p | 1
      have hgcd_eq_p : (n : ℕ).gcd p = p := Nat.gcd_eq_right hp_dvd
      rw [hgcd_eq_p] at hmem
      -- Step 3.1.5: p | 1 contradicts p > 1 (since p is prime)
      have hp_eq_1 : p = 1 := Nat.eq_one_of_dvd_one hmem
      -- Convert Prime p to Nat.Prime p to access one_lt
      have hp_nat_prime : Nat.Prime p := Nat.prime_iff.mpr hp_prime
      have hp_gt_1 : 1 < p := hp_nat_prime.one_lt
      omega

    -- Step 3.2: H is maximal (for any K with H ≤ K, either K = H or K = ⊤)
    · intro K hHK
      -- Step 3.2.1: K is a subgroup of cyclic G, so K is cyclic and K = zpowers k for some k
      haveI : IsCyclic K := Subgroup.isCyclic K
      obtain ⟨k, hk⟩ := IsCyclic.exists_generator (α := K)

      -- Step 3.2.2: k ∈ K ≤ G = closure {x}, so k = x^m for some m
      have hk_in_G : (k : G) ∈ closure ({x} : Set G) := by
        rw [hclosure_top]; exact mem_top k
      rw [← zpowers_eq_closure, mem_zpowers_iff] at hk_in_G
      obtain ⟨m, hkm⟩ := hk_in_G

      -- Step 3.2.3: K = zpowers k (the subgroup generated by k)
      have hK_eq : K = zpowers (k : G) := by
        ext y
        constructor
        · intro hy
          specialize hk ⟨y, hy⟩
          rw [mem_zpowers_iff] at hk ⊢
          obtain ⟨j, hj⟩ := hk
          use j
          exact Subtype.ext_iff.mp hj
        · intro hy
          rw [mem_zpowers_iff] at hy
          obtain ⟨j, hj⟩ := hy
          rw [← hj]
          exact zpow_mem k.property j

      -- Step 3.2.4: x^p ∈ K since H ≤ K and x^p generates H
      have hxp_in_K : x ^ p ∈ K := by
        rw [hH, ← zpowers_eq_closure] at hHK
        exact hHK (mem_zpowers (x ^ p))

      -- Step 3.2.5: Rewrite k = x^m, so K = zpowers(x^m)
      have hK_eq_m : K = zpowers (x ^ m) := by rw [hK_eq, hkm]

      -- Step 3.2.6: x^p ∈ zpowers(x^m), extract modular condition
      rw [hK_eq_m] at hxp_in_K
      rw [mem_zpowers_iff] at hxp_in_K
      obtain ⟨j, hj⟩ := hxp_in_K
      -- (x^m)^j = x^p means m*j ≡ p (mod n)
      rw [← zpow_mul, ← zpow_natCast x p, zpow_eq_zpow_iff_modEq, hx] at hj

      -- Step 3.2.7: Extract gcd(n, |m|) | p from the modular equality m*j ≡ p (mod n)
      have hgcd_dvd_p : (n : ℕ).gcd m.natAbs ∣ p := by
        rw [Int.ModEq] at hj
        have hdvd_n : ((n : ℕ).gcd m.natAbs : ℤ) ∣ (n : ℤ) :=
          Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left n m.natAbs)
        have hdvd_m : ((n : ℕ).gcd m.natAbs : ℤ) ∣ m := by
          have h := Nat.gcd_dvd_right (n : ℕ) m.natAbs
          -- gcd | |m| as naturals, need to show gcd | m as integers
          -- Use: Int.natCast_dvd_natCast and Int.natAbs_dvd
          -- (n : ℤ) ∣ a ↔ n ∣ a.natAbs (for natural n)
          rw [Int.natCast_dvd]
          exact h
        have hdvd_mj : ((n : ℕ).gcd m.natAbs : ℤ) ∣ m * j := dvd_mul_of_dvd_left hdvd_m j
        have hdiff : (n : ℤ) ∣ (m * j - (p : ℤ)) := by
          rw [Int.dvd_iff_emod_eq_zero, Int.sub_emod, hj, sub_self, Int.zero_emod]
        have hgcd_dvd_diff : ((n : ℕ).gcd m.natAbs : ℤ) ∣ (m * j - (p : ℤ)) :=
          dvd_trans hdvd_n hdiff
        have : ((n : ℕ).gcd m.natAbs : ℤ) ∣ (m * j - (m * j - (p : ℤ))) :=
          dvd_sub hdvd_mj hgcd_dvd_diff
        simp only [sub_sub_cancel] at this
        exact Int.natCast_dvd_natCast.mp this

      -- Step 3.2.8: Since p is prime and gcd | p, either gcd = 1 or gcd = p
      -- Convert Prime p to Nat.Prime p to access eq_one_or_self_of_dvd
      have hp_nat_prime : Nat.Prime p := Nat.prime_iff.mpr hp_prime
      rcases hp_nat_prime.eq_one_or_self_of_dvd ((n : ℕ).gcd m.natAbs) hgcd_dvd_p with
          hgcd_eq_1 | hgcd_eq_p

      -- Step 3.2.8.1: Case gcd(n, |m|) = 1 → K = ⊤
      · right
        rw [eq_top_iff, ← hclosure_top, ← zpowers_eq_closure, zpowers_le]
        -- Need: x ∈ K = zpowers(x^m)
        rw [hK_eq_m, mem_zpowers_iff]
        -- Find k such that (x^m)^k = x, i.e., m*k ≡ 1 (mod n)
        use (n : ℕ).gcdB m.natAbs * (if 0 ≤ m then 1 else -1)
        -- Goal: (x ^ m) ^ (...) = x
        -- We need to show x ^ (m * k) = x, i.e., m * k ≡ 1 (mod n)
        rw [← zpow_mul]
        have hbez := Nat.gcd_eq_gcd_ab (n : ℕ) m.natAbs
        rw [hgcd_eq_1] at hbez
        -- Compute m * (gcdB * sign) = |m| * gcdB
        have h1 : m * ((n : ℕ).gcdB m.natAbs * if 0 ≤ m then 1 else -1) =
            (m.natAbs : ℤ) * (n : ℕ).gcdB m.natAbs := by
          by_cases h_nonneg : 0 ≤ m
          -- Case 1: m ≥ 0, so m = |m|
          · rw [if_pos h_nonneg, mul_one]
            congr 1
            exact (Int.natAbs_of_nonneg h_nonneg).symm
          -- Case 2: m < 0, so m = -|m|
          · rw [if_neg h_nonneg, mul_neg_one]
            push_neg at h_nonneg
            -- m < 0, so m = -|m|
            have habs : m = -(m.natAbs : ℤ) := Int.eq_neg_natAbs_of_nonpos (le_of_lt h_nonneg)
            -- Simplify (-↑m.natAbs).natAbs = m.natAbs
            have h_neg_natabs : (-(m.natAbs : ℤ)).natAbs = m.natAbs := Int.natAbs_neg (m.natAbs : ℤ)
            rw [habs, h_neg_natabs]
            -- Goal: -(↑m.natAbs * -(↑n).gcdB m.natAbs) = ↑m.natAbs * (↑n).gcdB m.natAbs
            ring
        rw [h1]
        -- From Bezout: n * gcdA + |m| * gcdB = 1, so |m| * gcdB = 1 - n * gcdA
        have h2 : (m.natAbs : ℤ) * (n : ℕ).gcdB m.natAbs =
            1 - (n : ℤ) * (n : ℕ).gcdA m.natAbs := by
          have hbez2 : (1 : ℤ) = (n : ℤ) * (n : ℕ).gcdA m.natAbs +
              (m.natAbs : ℤ) * (n : ℕ).gcdB m.natAbs := by
            rw [← hbez]
            norm_cast
          linarith
        rw [h2]
        -- Need: x ^ (1 - n * gcdA) = x
        -- x ^ (1 - n * gcdA) = x ^ 1 * x ^ (-(n * gcdA)) = x * (x^n)^(-gcdA) = x * 1 = x
        -- Since x^n = 1 (order of x is n)
        rw [sub_eq_add_neg, zpow_add, zpow_one, zpow_neg, zpow_mul]
        -- Now goal: x * ((x ^ ↑↑n) ^ gcdA)⁻¹ = x
        -- We need x^n = 1
        -- Note: n : ℕ+ so ↑n : ℕ and ↑↑n : ℤ (two coercions)
        have hxn_eq_1 : x ^ (n : ℕ) = 1 := by
          rw [← hx]
          exact pow_orderOf_eq_one x
        -- The goal has x ^ ↑↑n, which is zpow with (↑n : ℤ) where n : ℕ+
        -- We need zpow_natCast to match: x ^ (↑(↑n : ℕ) : ℤ) = x ^ (↑n : ℕ)
        have h_zpow_eq : x ^ ((n : ℕ) : ℤ) = x ^ (n : ℕ) := zpow_natCast x (n : ℕ)
        rw [h_zpow_eq, hxn_eq_1]
        simp only [one_zpow, inv_one, mul_one]

      -- Step 3.2.8.2: Case gcd(n, |m|) = p → K = H
      · left
        rw [hH, ← zpowers_eq_closure, hK_eq_m]
        -- zpowers(x^m) = zpowers(x^p)
        -- First: zpowers(x^m) = zpowers(x^|m|)
        rw [zpowers_zpow_eq_zpowers_natAbs]
        -- Then: zpowers(x^|m|) = zpowers(x^gcd(n,|m|)) = zpowers(x^p)
        rw [zpowers_pow_eq_zpowers_gcd, hx, hgcd_eq_p]

  /-
    ============================================================================
    STEP 4: (⇐) If H is maximal, then H = closure {x^p} for some prime p | n
    ============================================================================
  -/
  · intro ⟨hH_ne_top, hH_max⟩
    -- Step 4.1: H is cyclic since it's a subgroup of cyclic G
    haveI : IsCyclic H := Subgroup.isCyclic H
    obtain ⟨h, hh⟩ := IsCyclic.exists_generator (α := H)

    -- Step 4.2: h ∈ H ≤ G = closure {x}, so h = x^m for some m
    have hh_in_G : (h : G) ∈ closure ({x} : Set G) := by
      rw [hclosure_top]; exact mem_top h
    rw [← zpowers_eq_closure, mem_zpowers_iff] at hh_in_G
    obtain ⟨m, hhm⟩ := hh_in_G

    -- Step 4.3: H = zpowers h (the subgroup generated by h)
    have hH_eq : H = zpowers (h : G) := by
      ext y
      constructor
      · intro hy
        specialize hh ⟨y, hy⟩
        rw [mem_zpowers_iff] at hh ⊢
        obtain ⟨j, hj⟩ := hh
        use j
        exact Subtype.ext_iff.mp hj
      · intro hy
        rw [mem_zpowers_iff] at hy
        obtain ⟨j, hj⟩ := hy
        rw [← hj]
        exact zpow_mem h.property j

    -- Step 4.4: Set d = gcd(n, |m|)
    let d := (n : ℕ).gcd m.natAbs

    -- Step 4.5: H = zpowers(x^d)
    -- This follows from: H = zpowers(h) = zpowers(x^m) = zpowers(x^|m|) = zpowers(x^gcd(n,|m|))
    have hH_eq_d : H = zpowers (x ^ d) := by
      rw [hH_eq, ← hhm]
      rw [zpowers_zpow_eq_zpowers_natAbs, zpowers_pow_eq_zpowers_gcd, hx]

    -- Step 4.6: d | n (since d = gcd(n, |m|))
    have hd_dvd : d ∣ n := Nat.gcd_dvd_left n m.natAbs

    -- Step 4.7: Since H ≠ ⊤, we have d > 1
    -- If d = 1, then zpowers(x^1) = zpowers(x) = closure {x} = ⊤, contradicting H ≠ ⊤
    have hd_gt_1 : 1 < d := by
      by_contra h_not
      push_neg at h_not
      -- d ≤ 1 and d = gcd(n, |m|) ≥ 1 since n > 0
      -- So d = 0 or d = 1
      have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left m.natAbs hn_pos
      have hd_eq_1 : d = 1 := by omega
      -- Case d = 1: zpowers(x^1) = zpowers(x) = closure {x} = ⊤, contradiction
      rw [hH_eq_d, hd_eq_1, pow_one, zpowers_eq_closure, hclosure_top] at hH_ne_top
      exact hH_ne_top rfl

    -- Step 4.8: Let p be a prime factor of d (exists since d > 1)
    have hd_ne_1 : d ≠ 1 := ne_of_gt hd_gt_1
    obtain ⟨p, hp_prime, hp_dvd_d⟩ := Nat.exists_prime_and_dvd hd_ne_1

    -- Step 4.9: p | d | n, so p | n
    have hp_dvd_n : p ∣ n := dvd_trans hp_dvd_d hd_dvd

    use p, hp_prime.prime, hp_dvd_n

    -- Step 4.10: Show H = closure {x^p} using maximality
    -- H = zpowers(x^d) and d | n with p | d
    -- We have H ≤ zpowers(x^p), and by maximality either H = zpowers(x^p) or zpowers(x^p) = ⊤

    -- Step 4.10.1: H ≤ zpowers(x^p)
    -- Since d = gcd(n, |m|) and p | d, we have x^d ∈ zpowers(x^p)
    have hH_le_p : H ≤ zpowers (x ^ p) := by
      rw [hH_eq_d, zpowers_le, mem_zpowers_pow_iff', hx]
      have hgcd_eq_p : (n : ℕ).gcd p = p := Nat.gcd_eq_right hp_dvd_n
      rw [hgcd_eq_p]
      exact hp_dvd_d

    -- Step 4.10.2: Apply maximality to get H = zpowers(x^p) or zpowers(x^p) = ⊤
    specialize hH_max (zpowers (x ^ p)) hH_le_p
    rcases hH_max with hH_eq_p | hp_eq_top
    -- Step 4.10.2.1: zpowers(x^p) = H → done
    -- Note: hH_eq_p says zpowers(x^p) = H, so we rewrite in reverse
    · rw [← hH_eq_p, zpowers_eq_closure]
    -- Step 4.10.2.2: zpowers(x^p) = ⊤ → contradiction
    -- If zpowers(x^p) = ⊤, then x ∈ zpowers(x^p), so gcd(n,p) | 1
    -- But gcd(n,p) = p since p | n, so p | 1, contradicting p > 1
    · exfalso
      rw [eq_top_iff, ← hclosure_top, ← zpowers_eq_closure, zpowers_le] at hp_eq_top
      have hmem : x ^ 1 ∈ zpowers (x ^ p) := by simp only [pow_one]; exact hp_eq_top
      rw [mem_zpowers_pow_iff', hx] at hmem
      have hgcd_eq_p : (n : ℕ).gcd p = p := Nat.gcd_eq_right hp_dvd_n
      rw [hgcd_eq_p] at hmem
      have hp_eq_1 : p = 1 := Nat.eq_one_of_dvd_one hmem
      have hp_gt_1 : 1 < p := hp_prime.one_lt
      omega
