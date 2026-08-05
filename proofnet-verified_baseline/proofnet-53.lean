import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

/-Informal Statement

Let $|G|=p q r$, where $p, q$ and $r$ are primes with $p < q < r$. Prove that $G$ has a normal Sylow subgroup for either $p, q$ or $r$.
-/

/-Informal Proof

Let $|G|=p q r$. We also assume $p<q<r$. We prove that $G$ has a normal Sylow subgroup of $p$, $q$ or $r$. Now, Let $n_p, n_q, n_r$ be the number of Sylow-p subgroup, Sylow-q subgroup, Sylow-r subgroup resp. So, we have $n_r=1+r k$ such that $1+r k \mid p q$. So, in this case as $r$ is greatest $n_r$ can be 1 or $p q$. We assume $n_r=p q$. Now we have $n_q=1+q k$ such that $1+q k \mid p r$. Now,as $p<q<r, n_q$ can be 1 or $r$, or $p r$. Assume that $n_q=r$. Now we turn to $n_p$. Again my similar method we can conclude $n_p$ can be $1, q, r$, or $q r$. We assume that $n_p$ is $q$. Now we count the number of elements of order $p, q, r$. Since $n_r=p q$, the number of elements of order $r$ is $p q(r-1)$. Since $n_q=r$, the number of elements of order $q$ is $(q-1) r$. And as $n_p=q$, the number of elements of order $p$ is $(p-1) q$. So, in total we get $p q(r-1)+(q-1) r+(p-$ 1) $q=p q r+q r-r-q=p q r+r(q-1)-r$. But observe that as $q>1, r(q-1)-r>$ 0 . So the number of elements exceeds $p q r$. So, it proves that at least $n_p$ or $n_q$ or $n_r$ is 1, which ultimately proves the result, because a unique Sylow-p subgroup is always normal.
-/

-- Step A: Helper lemma: divisors of a product of two distinct primes
lemma dvd_prime_mul_options {a b n : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b)
    (hn : n ∣ a * b) : n = 1 ∨ n = a ∨ n = b ∨ n = a * b := by
  have hn_pos : 0 < n := Nat.pos_of_dvd_of_pos hn (Nat.mul_pos ha.pos hb.pos)
  have hn_le : n ≤ a * b := Nat.le_of_dvd (Nat.mul_pos ha.pos hb.pos) hn
  by_cases h1 : n = 1
  · left; exact h1
  by_cases ha' : n = a
  · right; left; exact ha'
  by_cases hb' : n = b
  · right; right; left; exact hb'
  · right; right; right
    -- Step A.1: Show a and b are coprime
    have hcoprime : Nat.Coprime a b := by
      rw [ha.coprime_iff_not_dvd]
      intro hdvd
      have := hb.eq_one_or_self_of_dvd a hdvd
      cases this with
      | inl h => exact ha.ne_one h
      | inr h => exact hab h
    -- Step A.2: Analyze divisibility using gcd
    have hga := Nat.gcd_dvd_right n a
    have hgb := Nat.gcd_dvd_right n b
    -- Step A.3: Show a | n
    have ha_dvd_n : a ∣ n := by
      rcases ha.eq_one_or_self_of_dvd (Nat.gcd n a) hga with h | h
      · -- gcd(n, a) = 1, so n | b
        have hn_dvd_b : n ∣ b := by
          have hcop : Nat.Coprime n a := by
            rw [Nat.Coprime, h]
          exact hcop.dvd_of_dvd_mul_left hn
        rcases hb.eq_one_or_self_of_dvd n hn_dvd_b with heq | heq
        · exact absurd heq h1
        · exact absurd heq hb'
      · -- gcd(n, a) = a, so a | n
        exact h ▸ Nat.gcd_dvd_left n a
    -- Step A.4: Show b | n
    have hb_dvd_n : b ∣ n := by
      rcases hb.eq_one_or_self_of_dvd (Nat.gcd n b) hgb with h | h
      · -- gcd(n, b) = 1, so n | a
        have hn_dvd_a : n ∣ a := by
          have hcop : Nat.Coprime n b := by
            rw [Nat.Coprime, h]
          exact hcop.dvd_of_dvd_mul_right hn
        rcases ha.eq_one_or_self_of_dvd n hn_dvd_a with heq | heq
        · exact absurd heq h1
        · exact absurd heq ha'
      · -- gcd(n, b) = b, so b | n
        exact h ▸ Nat.gcd_dvd_left n b
    -- Step A.5: Since a | n and b | n and gcd(a,b) = 1, we have a*b | n
    have hab_dvd : a * b ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcoprime ha_dvd_n hb_dvd_n
    -- Step A.6: Since n | a*b and a*b | n, we have n = a*b
    exact Nat.dvd_antisymm hn hab_dvd

-- Step B: Helper to compute factorization at r for p * q * r
lemma factorization_pqr_at_r {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpr : p ≠ r) (hqr : q ≠ r) :
    (p * q * r).factorization r = 1 := by
  rw [Nat.factorization_mul (Nat.mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero]
  rw [Nat.factorization_mul hp.ne_zero hq.ne_zero]
  simp only [Finsupp.add_apply]
  rw [Nat.Prime.factorization_self hr]
  rw [hp.factorization, hq.factorization]
  simp only [Finsupp.single_apply]
  simp only [if_neg hpr, if_neg hqr, add_zero]

-- Step C: Helper to compute factorization at q for p * q * r
lemma factorization_pqr_at_q {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hqr : q ≠ r) :
    (p * q * r).factorization q = 1 := by
  rw [Nat.factorization_mul (Nat.mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero]
  rw [Nat.factorization_mul hp.ne_zero hq.ne_zero]
  simp only [Finsupp.add_apply]
  rw [Nat.Prime.factorization_self hq]
  rw [hp.factorization, hr.factorization]
  simp only [Finsupp.single_apply]
  simp only [if_neg hpq, if_neg hqr.symm, add_zero, zero_add]

-- Step D: Helper to compute factorization at p for p * q * r
lemma factorization_pqr_at_p {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) :
    (p * q * r).factorization p = 1 := by
  rw [Nat.factorization_mul (Nat.mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero]
  rw [Nat.factorization_mul hp.ne_zero hq.ne_zero]
  simp only [Finsupp.add_apply]
  rw [Nat.Prime.factorization_self hp]
  rw [hq.factorization, hr.factorization]
  simp only [Finsupp.single_apply]
  simp only [if_neg hpq.symm, if_neg hpr.symm, add_zero]

-- Step E: Element count contradiction helper using integer arithmetic
-- This proves that the element count exceeds |G| when n_r = pq, n_q ≥ r*(q-1), n_p ≥ q*(p-1)
-- The key insight is that (r-1)(q-1) > 0 when r > q > 1
lemma element_count_exceeds {p q r : ℕ} (hp : p ≥ 2) (hq : q ≥ 3) (hr_ge_q1 : r ≥ q + 1) :
    (p : ℤ) * q * r < p * q * (r - 1) + r * (q - 1) + q * (p - 1) + 1 := by
  have hp_pos : (0 : ℤ) < p := by linarith
  have hq_pos : (0 : ℤ) < q := by linarith
  have hr_pos : (0 : ℤ) < r := by
    have : (q : ℤ) + 1 ≤ r := Int.ofNat_le.mpr hr_ge_q1
    linarith
  -- Simplify: LHS = pqr
  -- RHS = pq(r-1) + r(q-1) + q(p-1) + 1 = pqr - pq + rq - r + pq - q + 1 = pqr + rq - r - q + 1
  -- RHS - LHS = rq - r - q + 1 = (r-1)(q-1)
  -- Since r ≥ q+1 ≥ 4 and q ≥ 3, (r-1)(q-1) ≥ 3*2 = 6 > 0
  have hrm1 : (r : ℤ) - 1 ≥ q := by
    have : (q : ℤ) + 1 ≤ r := Int.ofNat_le.mpr hr_ge_q1
    linarith
  have hqm1 : (q : ℤ) - 1 ≥ 2 := by linarith
  nlinarith

-- Step F: Element counting bound - elements of different prime orders are disjoint
-- For a finite group G with |G| = pqr (distinct primes), the non-identity elements of
-- orders p, q, r are pairwise disjoint. This is because:
-- 1. An element has a unique order
-- 2. Order divides group order, so for elements g ∈ G: orderOf g ∈ divisors of pqr
-- 3. Elements of prime order s are exactly in Sylow s-subgroups
-- The key lemma: if g has order s (prime), then g cannot have order t (different prime)
lemma order_prime_ne_of_ne {G : Type*} [Group G] {g : G} {p q : ℕ}
    (_ : p.Prime) (_ : q.Prime) (hpq : p ≠ q) (hg_ord : orderOf g = p) :
    orderOf g ≠ q := by
  rw [hg_ord]
  exact hpq

-- Step G: Helper lemma for n_q = pr case with q ≥ 2p
-- (q - p) * q ≥ p * q when q ≥ 2p
lemma sub_mul_ge_mul_pq (p q : ℕ) (hq_ge_2p : q ≥ 2 * p) : (q - p) * q ≥ p * q := by
  have h2pq_le_q2 : q * q ≥ 2 * p * q := by
    calc q * q ≥ (2 * p) * q := Nat.mul_le_mul_right q hq_ge_2p
      _ = 2 * p * q := by ring
  have hsub : (q - p) * q = q * q - p * q := Nat.sub_mul q p q
  rw [hsub]
  have h : p * q + p * q = 2 * p * q := by ring
  have h' : p * q + p * q ≤ q * q := by linarith
  exact Nat.le_sub_of_add_le h'

-- Division bound for n_q = pr case
lemma div_bound_pq (p q : ℕ) (_ : p ≥ 2) (hq_ge_2p : q ≥ 2 * p) (hqmp_pos : 0 < q - p) :
    (p * q - 1) / (q - p) ≤ q := by
  have h1 : (q - p) * q ≥ p * q := sub_mul_ge_mul_pq p q hq_ge_2p
  have h2 : (q - p) * q ≥ p * q - 1 := Nat.le_trans (Nat.sub_le _ _) h1
  calc (p * q - 1) / (q - p) ≤ ((q - p) * q) / (q - p) := Nat.div_le_div_right h2
    _ = q := Nat.mul_div_cancel_left q hqmp_pos

-- Main helper for n_r = pq, n_q = pr case with q ≥ 2p
lemma nq_pr_case_q_ge_2p {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (_ : r.Prime)
    (hpq : p < q) (hqr : q < r) (hq_ge_2p : q ≥ 2 * p)
    (hr_dvd_pqm1 : r ∣ p * q - 1) (hq_dvd_prm1 : q ∣ p * r - 1) : False := by
  have hp_ge_2 : p ≥ 2 := hp.two_le
  have hq_ge_3 : q ≥ 3 := by omega
  have hr_ge_4 : r ≥ 4 := by omega
  have hq_pos : 0 < q := hq.pos
  have hp_pos : 0 < p := hp.pos
  -- From r | pq - 1
  have hpr_ge_8 : p * r ≥ 8 := by
    have h1 : p * r ≥ 2 * 4 := Nat.mul_le_mul hp_ge_2 hr_ge_4
    omega
  have h1_le_pr : 1 ≤ p * r := by omega
  have h_pqm1_pos : p * q - 1 > 0 := by
    have h1 : p * q ≥ 2 * 3 := Nat.mul_le_mul hp_ge_2 (by omega : q ≥ 3)
    omega
  obtain ⟨k, hk⟩ := hr_dvd_pqm1
  have hpqm1_eq_kr : p * q - 1 = k * r := by linarith [hk, mul_comm r k]
  have hk_pos : k ≥ 1 := by
    by_contra hk_zero; push_neg at hk_zero
    simp only [Nat.lt_one_iff.mp hk_zero, zero_mul] at hpqm1_eq_kr
    omega
  -- pr mod q = 1
  have hpr_mod_q : (p * r) % q = 1 := by
    obtain ⟨m, hm⟩ := hq_dvd_prm1
    have hpr_eq : p * r = q * m + 1 := by omega
    calc (p * r) % q = (q * m + 1) % q := by rw [hpr_eq]
      _ = 1 := by simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < q)]
  -- kr mod q = q - 1
  have hkr_mod_q : (k * r) % q = q - 1 := by
    have hpqm1_mod : (p * q - 1) % q = q - 1 := by
      have h3 : p * q - 1 = (p - 1) * q + (q - 1) := by
        have hp1 : p ≥ 1 := by omega
        calc p * q - 1 = (p - 1 + 1) * q - 1 := by rw [Nat.sub_add_cancel hp1]
          _ = (p - 1) * q + q - 1 := by ring_nf
          _ = (p - 1) * q + (q - 1) := by omega
      calc (p * q - 1) % q = ((p - 1) * q + (q - 1)) % q := by rw [h3]
        _ = (q - 1) := by simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : q - 1 < q)]
    rw [← hpqm1_eq_kr]; exact hpqm1_mod
  -- k % q = q - p
  have hk_mod_q : k % q = q - p := by
    have hp_lt_q : p < q := hpq
    have hp_mod_q : p % q = p := Nat.mod_eq_of_lt hp_lt_q
    have hqmp_lt_q : q - p < q := by omega
    have h1 : (k * r * p) % q = ((q - 1) * p) % q := by
      calc (k * r * p) % q = ((k * r) % q * (p % q)) % q := Nat.mul_mod (k * r) p q
        _ = ((q - 1) * p) % q := by rw [hkr_mod_q, hp_mod_q]
    have h2 : (k * r * p) % q = k % q := by
      have heq1 : k * r * p = k * (p * r) := by ring
      calc (k * r * p) % q = (k * (p * r)) % q := by rw [heq1]
        _ = ((k % q) * ((p * r) % q)) % q := Nat.mul_mod k (p * r) q
        _ = ((k % q) * 1) % q := by rw [hpr_mod_q]
        _ = (k % q) % q := by ring_nf
        _ = k % q := Nat.mod_mod _ _
    have h3 : k % q = ((q - 1) * p) % q := by rw [← h2, h1]
    have h4 : ((q - 1) * p) % q = q - p := by
      have hp1 : p ≥ 1 := by omega
      have h_qm1_p : (q - 1) * p = q * p - p := Nat.sub_one_mul q p
      have h_pm1_q : (p - 1) * q = p * q - q := Nat.sub_one_mul p q
      have hqp_comm : q * p = p * q := mul_comm q p
      have heq : (q - 1) * p = (p - 1) * q + (q - p) := by
        calc (q - 1) * p = q * p - p := h_qm1_p
          _ = p * q - p := by rw [hqp_comm]
          _ = (p * q - q) + (q - p) := by
              have hpq_ge_q : p * q ≥ q := Nat.le_mul_of_pos_left q hp_pos
              have hpq_ge_p : p * q ≥ p := Nat.le_mul_of_pos_right p hq_pos
              omega
          _ = (p - 1) * q + (q - p) := by rw [← h_pm1_q]
      calc ((q - 1) * p) % q = ((p - 1) * q + (q - p)) % q := by rw [heq]
        _ = (q - p) := by simp [Nat.add_mod, Nat.mod_eq_of_lt hqmp_lt_q]
    rw [h3, h4]
  -- k ≥ q - p
  have hk_ge_qmp : k ≥ q - p := by
    by_contra h_lt; push_neg at h_lt
    have hk_lt_q : k < q := by omega
    rw [Nat.mod_eq_of_lt hk_lt_q] at hk_mod_q
    omega
  -- r ≤ (pq - 1)/(q - p)
  have hqmp_pos : 0 < q - p := by omega
  have hr_le : r ≤ (p * q - 1) / (q - p) := by
    have hk_pos' : 0 < k := by omega
    have h1 : r = (p * q - 1) / k := by
      rw [hpqm1_eq_kr]
      exact (Nat.mul_div_cancel_left r hk_pos').symm
    rw [h1]
    exact Nat.div_le_div_left hk_ge_qmp hqmp_pos
  have hdiv_le_q : (p * q - 1) / (q - p) ≤ q := div_bound_pq p q hp_ge_2 hq_ge_2p hqmp_pos
  omega

-- ============================================================================
-- Sylow Element Counting Infrastructure
-- ============================================================================
-- These lemmas establish the group-theoretic bound used in the element counting
-- argument for the main theorem.

section SylowElementCounting

open Fintype Subgroup Set Sylow
open scoped BigOperators Classical

variable {G' : Type*} [Group G'] [Fintype G']

noncomputable section

-- Define non-identity elements of a Sylow subgroup as a Finset
def sylowNonId' (s : ℕ) [Fact s.Prime] (P : Sylow s G') : Finset G' :=
  (P.toSubgroup : Set G').toFinset \ {1}

-- Cardinality of sylowNonId' when |P| = s
lemma card_sylowNonId' (s : ℕ) [Fact s.Prime] (P : Sylow s G')
    (hP : Nat.card P.toSubgroup = s) :
    (sylowNonId' s P).card = s - 1 := by
  unfold sylowNonId'
  have hP' : Fintype.card P.toSubgroup = s := by
    simp only [Nat.card_eq_fintype_card] at hP; exact hP
  have h_inter : ({1} : Finset G') ∩ (P.toSubgroup : Set G').toFinset = {1} := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_singleton, Set.mem_toFinset, SetLike.mem_coe]
    constructor
    · intro ⟨hx, _⟩; exact hx
    · intro hx; exact ⟨hx, hx ▸ P.toSubgroup.one_mem⟩
  have h1 : ((P.toSubgroup : Set G').toFinset \ {1}).card
          = (P.toSubgroup : Set G').toFinset.card - ({1} ∩ (P.toSubgroup : Set G').toFinset).card :=
    Finset.card_sdiff
  have h2 : ({1} ∩ (P.toSubgroup : Set G').toFinset).card = 1 := by
    rw [h_inter]; exact Finset.card_singleton 1
  have h3 : (P.toSubgroup : Set G').toFinset.card = s := by
    simp only [Set.toFinset_card, SetLike.coe_sort_coe, hP']
  rw [h1, h2, h3]

-- Two distinct Sylow s-subgroups of prime order s share only identity
lemma sylow_same_prime_disjoint' (s : ℕ) [Fact s.Prime] (P Q : Sylow s G')
    (hP : Nat.card P.toSubgroup = s) (hQ : Nat.card Q.toSubgroup = s) (hPQ : P ≠ Q) :
    ((P.toSubgroup : Set G') \ {1}) ∩ ((Q.toSubgroup : Set G') \ {1}) = ∅ := by
  ext g
  simp only [Set.mem_inter_iff, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff,
             Set.mem_empty_iff_false, iff_false, not_and, and_imp]
  intro hgP hg_ne1 hgQ _
  have hFintype_P : Fintype P.toSubgroup := Fintype.ofFinite _
  have hFintype_Q : Fintype Q.toSubgroup := Fintype.ofFinite _
  have hP' : Fintype.card P.toSubgroup = s := by
    simp only [Nat.card_eq_fintype_card] at hP; exact hP
  have hQ' : Fintype.card Q.toSubgroup = s := by
    simp only [Nat.card_eq_fintype_card] at hQ; exact hQ
  have h_ord_dvd : orderOf g ∣ s := by
    have h1 : orderOf (⟨g, hgP⟩ : P.toSubgroup) ∣ Fintype.card P.toSubgroup := orderOf_dvd_card
    have h2 : orderOf (⟨g, hgP⟩ : P.toSubgroup) = orderOf g := (Subgroup.orderOf_coe _).symm
    rw [h2, hP'] at h1; exact h1
  have h_ord_eq : orderOf g = s :=
    (Fact.out : s.Prime).eq_one_or_self_of_dvd _ h_ord_dvd |>.resolve_left
      (fun h => hg_ne1 (orderOf_eq_one_iff.mp h))
  have h_zpowers_card : Nat.card (zpowers g) = s := by rw [Nat.card_zpowers, h_ord_eq]
  have h_le_P : zpowers g ≤ P.toSubgroup := Subgroup.zpowers_le_of_mem hgP
  have h_eq_P : zpowers g = P.toSubgroup := by
    apply le_antisymm h_le_P
    intro x hx
    by_contra h_not
    have h_strict : zpowers g < P.toSubgroup := lt_of_le_of_ne h_le_P (fun h => h_not (h ▸ hx))
    have h_card_lt : Nat.card (zpowers g) < Nat.card P.toSubgroup := by
      have h_ssubset : (zpowers g : Set G') ⊂ (P.toSubgroup : Set G') := h_strict
      have h_finite : (P.toSubgroup : Set G').Finite := Set.toFinite _
      exact h_finite.card_lt_card h_ssubset
    rw [h_zpowers_card, hP] at h_card_lt
    exact Nat.lt_irrefl s h_card_lt
  have h_le_Q : zpowers g ≤ Q.toSubgroup := Subgroup.zpowers_le_of_mem hgQ
  have h_eq_Q : zpowers g = Q.toSubgroup := by
    apply le_antisymm h_le_Q
    intro x hx
    by_contra h_not
    have h_strict : zpowers g < Q.toSubgroup := lt_of_le_of_ne h_le_Q (fun h => h_not (h ▸ hx))
    have h_card_lt : Nat.card (zpowers g) < Nat.card Q.toSubgroup := by
      have h_ssubset : (zpowers g : Set G') ⊂ (Q.toSubgroup : Set G') := h_strict
      have h_finite : (Q.toSubgroup : Set G').Finite := Set.toFinite _
      exact h_finite.card_lt_card h_ssubset
    rw [h_zpowers_card, hQ] at h_card_lt
    exact Nat.lt_irrefl s h_card_lt
  have : P.toSubgroup = Q.toSubgroup := by rw [← h_eq_P, h_eq_Q]
  exact hPQ (Sylow.ext this)

-- Sylow subgroups of different primes share only identity
lemma sylow_diff_prime_disjoint' (q' r' : ℕ) [Fact q'.Prime] [Fact r'.Prime]
    (hqr : q' ≠ r') (Q : Sylow q' G') (R : Sylow r' G') :
    ((Q.toSubgroup : Set G') \ {1}) ∩ ((R.toSubgroup : Set G') \ {1}) = ∅ := by
  ext g
  simp only [Set.mem_inter_iff, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff,
             Set.mem_empty_iff_false, iff_false, not_and, and_imp]
  intro hgQ hg_ne1 hgR _
  have hFintype_Q : Fintype Q.toSubgroup := Fintype.ofFinite _
  have hFintype_R : Fintype R.toSubgroup := Fintype.ofFinite _
  have h_ord_dvd_Q : orderOf g ∣ Fintype.card Q.toSubgroup := by
    have h1 : orderOf (⟨g, hgQ⟩ : Q.toSubgroup) ∣ Fintype.card Q.toSubgroup := orderOf_dvd_card
    have h2 : orderOf (⟨g, hgQ⟩ : Q.toSubgroup) = orderOf g := (Subgroup.orderOf_coe _).symm
    rw [h2] at h1; exact h1
  have h_ord_dvd_R : orderOf g ∣ Fintype.card R.toSubgroup := by
    have h1 : orderOf (⟨g, hgR⟩ : R.toSubgroup) ∣ Fintype.card R.toSubgroup := orderOf_dvd_card
    have h2 : orderOf (⟨g, hgR⟩ : R.toSubgroup) = orderOf g := (Subgroup.orderOf_coe _).symm
    rw [h2] at h1; exact h1
  obtain ⟨kq, hkq⟩ : ∃ k, Fintype.card Q.toSubgroup = q' ^ k := by
    have h := Sylow.card_eq_multiplicity (G := G') (p := q') Q
    simp only [Nat.card_eq_fintype_card] at h; exact ⟨_, h⟩
  obtain ⟨kr, hkr⟩ : ∃ k, Fintype.card R.toSubgroup = r' ^ k := by
    have h := Sylow.card_eq_multiplicity (G := G') (p := r') R
    simp only [Nat.card_eq_fintype_card] at h; exact ⟨_, h⟩
  rw [hkq] at h_ord_dvd_Q
  rw [hkr] at h_ord_dvd_R
  have hcop : Nat.Coprime (q' ^ kq) (r' ^ kr) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes (Fact.out) (Fact.out)).mpr hqr)
  have h_ord_dvd_gcd : orderOf g ∣ Nat.gcd (q' ^ kq) (r' ^ kr) := Nat.dvd_gcd h_ord_dvd_Q h_ord_dvd_R
  rw [hcop] at h_ord_dvd_gcd
  have h_ord_one : orderOf g = 1 := Nat.eq_one_of_dvd_one h_ord_dvd_gcd
  exact hg_ne1 (orderOf_eq_one_iff.mp h_ord_one)

-- Disjointness of sylowNonId' for Finsets
lemma sylowNonId_disjoint' (s : ℕ) [Fact s.Prime] (P Q : Sylow s G')
    (hP : Nat.card P.toSubgroup = s) (hQ : Nat.card Q.toSubgroup = s) (hPQ : P ≠ Q) :
    Disjoint (sylowNonId' s P) (sylowNonId' s Q) := by
  rw [Finset.disjoint_iff_ne]
  intro g hgP h hgQ
  simp only [sylowNonId', Finset.mem_sdiff, Set.mem_toFinset, SetLike.mem_coe,
             Finset.mem_singleton] at hgP hgQ
  obtain ⟨hgP_mem, hg_neP⟩ := hgP
  obtain ⟨hgQ_mem, _⟩ := hgQ
  intro heq; subst heq
  have h_disj := sylow_same_prime_disjoint' s P Q hP hQ hPQ
  have : g ∈ ((P.toSubgroup : Set G') \ {1}) ∩ ((Q.toSubgroup : Set G') \ {1}) :=
    ⟨⟨hgP_mem, hg_neP⟩, ⟨hgQ_mem, hg_neP⟩⟩
  rw [h_disj] at this
  exact this

-- The union of sylowNonId' across all Sylow s-subgroups
def allSylowNonId' (s : ℕ) [Fact s.Prime] : Finset G' :=
  Finset.univ.biUnion (sylowNonId' s (G' := G'))

-- Cardinality = n_s * (s - 1)
lemma card_allSylowNonId' (s : ℕ) [Fact s.Prime]
    (hAll : ∀ P : Sylow s G', Nat.card P.toSubgroup = s) :
    (allSylowNonId' (G' := G') s).card = Fintype.card (Sylow s G') * (s - 1) := by
  unfold allSylowNonId'
  rw [Finset.card_biUnion]
  · simp only [card_sylowNonId' _ _ (hAll _)]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  · intro P _ Q _ hPQ
    exact sylowNonId_disjoint' s P Q (hAll P) (hAll Q) hPQ

-- Disjointness of allSylowNonId' for different primes
lemma allSylowNonId_disjoint' (q' r' : ℕ) [Fact q'.Prime] [Fact r'.Prime] (hqr : q' ≠ r') :
    Disjoint (allSylowNonId' (G' := G') q') (allSylowNonId' (G' := G') r') := by
  rw [Finset.disjoint_iff_ne]
  intro g hgQ h hgR
  simp only [allSylowNonId', Finset.mem_biUnion, Finset.mem_univ, true_and,
             sylowNonId', Finset.mem_sdiff, Set.mem_toFinset, SetLike.mem_coe,
             Finset.mem_singleton] at hgQ hgR
  obtain ⟨Q, hgQ_mem, hg_neQ⟩ := hgQ
  obtain ⟨R, hgR_mem, hg_neR⟩ := hgR
  intro heq; subst heq
  have h_disj := sylow_diff_prime_disjoint' q' r' hqr Q R
  have : g ∈ ((Q.toSubgroup : Set G') \ {1}) ∩ ((R.toSubgroup : Set G') \ {1}) :=
    ⟨⟨hgQ_mem, hg_neQ⟩, ⟨hgR_mem, hg_neR⟩⟩
  rw [h_disj] at this
  exact this

-- The element counting bound
lemma elem_count_le_card' (q' r' : ℕ) [Fact q'.Prime] [Fact r'.Prime] (hqr : q' ≠ r')
    (hAllQ : ∀ Q : Sylow q' G', Nat.card Q.toSubgroup = q')
    (hAllR : ∀ R : Sylow r' G', Nat.card R.toSubgroup = r') :
    1 + Fintype.card (Sylow q' G') * (q' - 1) + Fintype.card (Sylow r' G') * (r' - 1) ≤ Fintype.card G' := by
  let S : Finset G' := insert (1 : G') ((allSylowNonId' (G' := G') q') ∪ (allSylowNonId' (G' := G') r'))
  have h_one_not_in : (1 : G') ∉ (allSylowNonId' (G' := G') q') ∪ (allSylowNonId' (G' := G') r') := by
    simp only [Finset.mem_union, allSylowNonId', Finset.mem_biUnion, Finset.mem_univ, true_and,
               sylowNonId', Finset.mem_sdiff, Set.mem_toFinset, SetLike.mem_coe,
               Finset.mem_singleton, not_or, not_exists, not_and]
    constructor <;> intro P <;> intro hP <;> simp
  have h_card_S : S.card = 1 + (allSylowNonId' (G' := G') q').card + (allSylowNonId' (G' := G') r').card := by
    rw [Finset.card_insert_of_notMem h_one_not_in]
    rw [Finset.card_union_of_disjoint (allSylowNonId_disjoint' q' r' hqr)]
    ring
  have h_S_le_G : S.card ≤ Fintype.card G' := Finset.card_le_univ S
  rw [card_allSylowNonId' q' hAllQ, card_allSylowNonId' r' hAllR] at h_card_S
  rw [h_card_S] at h_S_le_G
  exact h_S_le_G

-- Final bound for the specific case: proves contradiction via element counting
lemma elem_count_bound_final' (p' q' r' : ℕ) [Fact p'.Prime] [Fact q'.Prime] [Fact r'.Prime]
    (hpq : p' < q') (hqr : q' < r')
    (hG' : Fintype.card G' = p' * q' * r')
    (hNumQ : Nat.card (Sylow q' G') = p' * r')
    (hNumR : Nat.card (Sylow r' G') = p' * q') :
    2 * p' * q' * r' - p' * q' - p' * r' + 1 ≤ p' * q' * r' := by
  have hqr_ne : q' ≠ r' := Nat.ne_of_lt hqr
  have hp_ne_q : p' ≠ q' := Nat.ne_of_lt hpq
  have hp_ne_r : p' ≠ r' := Nat.ne_of_lt (Nat.lt_trans hpq hqr)
  have hAllQ : ∀ Q : Sylow q' G', Nat.card Q.toSubgroup = q' := fun Q => by
    have hFintype : Fintype Q.toSubgroup := Fintype.ofFinite _
    have h := Sylow.card_eq_multiplicity (G := G') (p := q') Q
    have hFactor : Nat.factorization (Fintype.card G') q' = 1 := by
      rw [hG']
      rw [Nat.factorization_mul (Nat.mul_ne_zero (Nat.Prime.ne_zero (Fact.out : p'.Prime))
                                                 (Nat.Prime.ne_zero (Fact.out : q'.Prime)))
                                (Nat.Prime.ne_zero (Fact.out : r'.Prime))]
      rw [Nat.factorization_mul (Nat.Prime.ne_zero (Fact.out : p'.Prime))
                                (Nat.Prime.ne_zero (Fact.out : q'.Prime))]
      simp only [Finsupp.add_apply]
      rw [(Fact.out : p'.Prime).factorization, (Fact.out : q'.Prime).factorization,
          (Fact.out : r'.Prime).factorization]
      simp [hp_ne_q, hqr_ne]
    simp only [Nat.card_eq_fintype_card] at h ⊢
    rw [h, hFactor, pow_one]
  have hAllR : ∀ R : Sylow r' G', Nat.card R.toSubgroup = r' := fun R => by
    have hFintype : Fintype R.toSubgroup := Fintype.ofFinite _
    have h := Sylow.card_eq_multiplicity (G := G') (p := r') R
    have hFactor : Nat.factorization (Fintype.card G') r' = 1 := by
      rw [hG']
      rw [Nat.factorization_mul (Nat.mul_ne_zero (Nat.Prime.ne_zero (Fact.out : p'.Prime))
                                                 (Nat.Prime.ne_zero (Fact.out : q'.Prime)))
                                (Nat.Prime.ne_zero (Fact.out : r'.Prime))]
      rw [Nat.factorization_mul (Nat.Prime.ne_zero (Fact.out : p'.Prime))
                                (Nat.Prime.ne_zero (Fact.out : q'.Prime))]
      simp only [Finsupp.add_apply]
      rw [(Fact.out : p'.Prime).factorization, (Fact.out : q'.Prime).factorization,
          (Fact.out : r'.Prime).factorization]
      simp [hp_ne_r, hqr_ne]
    simp only [Nat.card_eq_fintype_card] at h ⊢
    rw [h, hFactor, pow_one]
  have h := elem_count_le_card' q' r' hqr_ne hAllQ hAllR
  simp only [Fintype.card_eq_nat_card] at h
  rw [hNumQ, hNumR] at h
  simp only [Nat.card_eq_fintype_card, hG'] at h
  -- h: 1 + p' * r' * (q' - 1) + p' * q' * (r' - 1) ≤ p' * q' * r'
  exfalso
  have hq_pos : q' ≥ 2 := Nat.Prime.two_le (Fact.out : q'.Prime)
  have hr_pos : r' ≥ 2 := Nat.Prime.two_le (Fact.out : r'.Prime)
  have hp_pos : p' ≥ 2 := Nat.Prime.two_le (Fact.out : p'.Prime)
  have hqr_bound : q' * r' ≥ q' + r' := by nlinarith
  have h_key : p' * q' * r' ≥ p' * q' + p' * r' := by
    calc p' * q' * r' = p' * (q' * r') := by ring
      _ ≥ p' * (q' + r') := Nat.mul_le_mul_left p' hqr_bound
      _ = p' * q' + p' * r' := by ring
  have hq_ge_1 : q' ≥ 1 := Nat.one_le_of_lt hq_pos
  have hr_ge_1 : r' ≥ 1 := Nat.one_le_of_lt hr_pos
  have hpr_sub : p' * r' * (q' - 1) + p' * r' = p' * r' * q' := by
    calc p' * r' * (q' - 1) + p' * r' = p' * r' * ((q' - 1) + 1) := by ring
      _ = p' * r' * q' := by rw [Nat.sub_add_cancel hq_ge_1]
  have hpq_sub : p' * q' * (r' - 1) + p' * q' = p' * q' * r' := by
    calc p' * q' * (r' - 1) + p' * q' = p' * q' * ((r' - 1) + 1) := by ring
      _ = p' * q' * r' := by rw [Nat.sub_add_cancel hr_ge_1]
  have hprq_eq : p' * r' * q' = p' * q' * r' := by ring
  have h_expanded : 1 + p' * r' * q' + p' * q' * r' ≤ p' * q' * r' + p' * r' + p' * q' := by
    have step1 : 1 + p' * r' * (q' - 1) + p' * q' * (r' - 1) + (p' * r' + p' * q')
               ≤ p' * q' * r' + (p' * r' + p' * q') := Nat.add_le_add_right h _
    have step2 : 1 + p' * r' * (q' - 1) + p' * q' * (r' - 1) + (p' * r' + p' * q')
               = 1 + (p' * r' * (q' - 1) + p' * r') + (p' * q' * (r' - 1) + p' * q') := by ring
    rw [step2, hpr_sub, hpq_sub] at step1
    have : p' * q' * r' + (p' * r' + p' * q') = p' * q' * r' + p' * r' + p' * q' := by ring
    rw [this] at step1
    exact step1
  rw [hprq_eq] at h_expanded
  have h_final : p' * q' * r' + 1 ≤ p' * r' + p' * q' := by omega
  omega

end

end SylowElementCounting

-- ============================================================================
-- Main Theorem
-- ============================================================================

theorem Dummit_Foote_exercise_4_5_16 {p q r : ℕ} {G : Type*} [Group G]
  [Fintype G]  (hpqr : p < q ∧ q < r)
  (hpqr1 : p.Prime ∧ q.Prime ∧ r.Prime)(hG : card G = p*q*r) :
  (∃ (P : Sylow p G), P.Normal) ∨ (∃ (P : Sylow q G), P.Normal) ∨ (∃ (P : Sylow r G), P.Normal) := by
  classical
  -- Step 1: Unpack the hypotheses and choose Sylow representatives.
  -- Step 1.1: Split the strict ordering hypothesis into `p < q`, `q < r`,
  -- and derive the transitive inequality `p < r`.
  obtain ⟨hpq, hqr⟩ := hpqr
  have hpr : p < r := Nat.lt_trans hpq hqr

  -- Step 1.2: Split the prime hypotheses so each prime can be used separately.
  obtain ⟨hp_prime, hq_prime, hr_prime⟩ := hpqr1

  -- Step 1.3: Register the prime hypotheses as instances for Sylow lemmas.
  haveI hpFact : Fact (Nat.Prime p) := ⟨hp_prime⟩
  haveI hqFact : Fact (Nat.Prime q) := ⟨hq_prime⟩
  haveI hrFact : Fact (Nat.Prime r) := ⟨hr_prime⟩

  -- Step 1.4: Pick one Sylow subgroup for each prime; these are used to compute indices.
  let P : Sylow p G := default
  let Q : Sylow q G := default
  let R : Sylow r G := default

  -- Step 1.5: Convert strict inequalities into pairwise non-equality of primes.
  have hpq_ne : p ≠ q := Nat.ne_of_lt hpq
  have hqr_ne : q ≠ r := Nat.ne_of_lt hqr
  have hpr_ne : p ≠ r := Nat.ne_of_lt hpr

  -- Step 2: Compute the Sylow indices from `|G| = p*q*r`.
  -- Step 2.1: The Sylow `r`-subgroup has order `r`, hence index `p*q`.
  have hIndexR : R.index = p * q := by
    -- Step 2.1.1: Compute `|R| = r` from the `r`-adic multiplicity of `|G|`.
    have hCardR : Fintype.card R = r := by
      have h := Sylow.card_eq_multiplicity (G := G) (p := r) R
      simp only [Nat.card_eq_fintype_card] at h
      have hFactor : Nat.factorization (Fintype.card G) r = 1 := by
        rw [hG]
        exact factorization_pqr_at_r hp_prime hq_prime hr_prime hpr_ne hqr_ne
      rw [h, hFactor, pow_one]
    -- Step 2.1.2: Use `index * subgroup_card = group_card` and cancel `r`.
    have hMul : R.index * Fintype.card R = Fintype.card G := by
      have h := (R : Subgroup G).index_mul_card
      simpa [Nat.card_eq_fintype_card] using h
    simp only [hCardR, hG] at hMul
    exact Nat.eq_of_mul_eq_mul_right hr_prime.pos hMul

  -- Step 2.2: The same computation gives the Sylow `q`-subgroup index `p*r`.
  have hIndexQ : Q.index = p * r := by
    -- Step 2.2.1: Compute `|Q| = q`.
    have hCardQ : Fintype.card Q = q := by
      have h := Sylow.card_eq_multiplicity (G := G) (p := q) Q
      simp only [Nat.card_eq_fintype_card] at h
      have hFactor : Nat.factorization (Fintype.card G) q = 1 := by
        rw [hG]
        exact factorization_pqr_at_q hp_prime hq_prime hr_prime hpq_ne hqr_ne
      rw [h, hFactor, pow_one]
    -- Step 2.2.2: Use the index-cardinality product and cancel `q`.
    have hMul : Q.index * Fintype.card Q = Fintype.card G := by
      have h := (Q : Subgroup G).index_mul_card
      simpa [Nat.card_eq_fintype_card] using h
    simp only [hCardQ, hG] at hMul
    have hEq' : Q.index * q = (p * r) * q := by ring_nf; ring_nf at hMul; exact hMul
    exact Nat.eq_of_mul_eq_mul_right hq_prime.pos hEq'

  -- Step 2.3: The Sylow `p`-subgroup has index `q*r`.
  have hIndexP : P.index = q * r := by
    -- Step 2.3.1: Compute `|P| = p`.
    have hCardP : Fintype.card P = p := by
      have h := Sylow.card_eq_multiplicity (G := G) (p := p) P
      simp only [Nat.card_eq_fintype_card] at h
      have hFactor : Nat.factorization (Fintype.card G) p = 1 := by
        rw [hG]
        exact factorization_pqr_at_p hp_prime hq_prime hr_prime hpq_ne hpr_ne
      rw [h, hFactor, pow_one]
    -- Step 2.3.2: Use the index-cardinality product and cancel `p`.
    have hMul : P.index * Fintype.card P = Fintype.card G := by
      have h := (P : Subgroup G).index_mul_card
      simpa [Nat.card_eq_fintype_card] using h
    simp only [hCardP, hG] at hMul
    have hEq' : P.index * p = (q * r) * p := by ring_nf; ring_nf at hMul; exact hMul
    exact Nat.eq_of_mul_eq_mul_right hp_prime.pos hEq'

  -- Step 3: Record Sylow divisibility and congruence constraints.
  -- Step 3.1: For `n_r`, Sylow gives `n_r | [G:R] = p*q` and `n_r ≡ 1 mod r`.
  have hNumR_dvd : Nat.card (Sylow r G) ∣ p * q := by simpa [hIndexR] using Sylow.card_dvd_index R
  have hNumR_mod : Nat.card (Sylow r G) ≡ 1 [MOD r] := card_sylow_modEq_one r G

  -- Step 3.2: For `n_q`, Sylow gives `n_q | [G:Q] = p*r` and `n_q ≡ 1 mod q`.
  have hNumQ_dvd : Nat.card (Sylow q G) ∣ p * r := by simpa [hIndexQ] using Sylow.card_dvd_index Q
  have hNumQ_mod : Nat.card (Sylow q G) ≡ 1 [MOD q] := card_sylow_modEq_one q G

  -- Step 3.3: For `n_p`, Sylow gives `n_p | [G:P] = q*r` and `n_p ≡ 1 mod p`.
  have hNumP_dvd : Nat.card (Sylow p G) ∣ q * r := by simpa [hIndexP] using Sylow.card_dvd_index P
  have hNumP_mod : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G

  -- Step 4: Set up arithmetic bounds and the uniqueness-implies-normal helper.
  -- Step 4.1: Prime lower bounds used throughout the modular arithmetic.
  have hp_ge_2 : p ≥ 2 := hp_prime.two_le
  have hq_ge_2 : q ≥ 2 := hq_prime.two_le
  have hr_ge_2 : r ≥ 2 := hr_prime.two_le
  have hq_ge_3 : q ≥ 3 := by omega

  -- Step 4.2: If the Sylow type has cardinality one, it is subsingleton,
  -- and the unique Sylow subgroup is normal.
  have normal_of_card_one : ∀ (s : ℕ) [Fact (Nat.Prime s)],
      Nat.card (Sylow s G) = 1 → ∃ (S : Sylow s G), S.Normal := by
    intro s _ hOne
    have hSubsingleton : Subsingleton (Sylow s G) := by
      have : Fintype (Sylow s G) := Fintype.ofFinite _
      have hcard_le : Fintype.card (Sylow s G) ≤ 1 := by
        simp only [Nat.card_eq_fintype_card] at hOne
        omega
      exact Fintype.card_le_one_iff_subsingleton.mp hcard_le
    exact ⟨default, Sylow.normal_of_subsingleton _⟩

  -- Step 5: Filter the possible values of `n_r`; if `n_r = 1`, finish.
  -- Step 5.1: Since `n_r | p*q`, the prime-product helper leaves
  -- only the four candidates `1`, `p`, `q`, and `p*q`.
  have hNumR_options := dvd_prime_mul_options hp_prime hq_prime hpq_ne hNumR_dvd

  -- Step 5.2: Exclude the candidate `n_r = p`, because `p < r` prevents `p ≡ 1 mod r`.
  have hp_not_one_mod_r : ¬ (p ≡ 1 [MOD r]) := by
    intro h
    have h1_le : 1 ≤ p := by omega
    have hdvd : r ∣ p - 1 := (Nat.modEq_iff_dvd' h1_le).mp h.symm
    by_cases hzero : p - 1 = 0
    · omega
    · have := Nat.le_of_dvd (Nat.pos_of_ne_zero hzero) hdvd; omega

  -- Step 5.3: Exclude the candidate `n_r = q`, because `q < r` prevents `q ≡ 1 mod r`.
  have hq_not_one_mod_r : ¬ (q ≡ 1 [MOD r]) := by
    intro h
    have h1_le : 1 ≤ q := by omega
    have hdvd : r ∣ q - 1 := (Nat.modEq_iff_dvd' h1_le).mp h.symm
    by_cases hzero : q - 1 = 0
    · omega
    · have := Nat.le_of_dvd (Nat.pos_of_ne_zero hzero) hdvd; omega

  -- Step 5.4: After applying the congruence, only `n_r = 1` or `n_r = p*q` remains.
  have hNumR_filtered : Nat.card (Sylow r G) = 1 ∨ Nat.card (Sylow r G) = p * q := by
    rcases hNumR_options with h1 | hp' | hq' | hpq'
    · left; exact h1
    · exfalso; exact hp_not_one_mod_r (hp' ▸ hNumR_mod)
    · exfalso; exact hq_not_one_mod_r (hq' ▸ hNumR_mod)
    · right; exact hpq'

  -- Step 5.5: If `n_r = 1`, the Sylow `r`-subgroup is normal and the proof is done.
  rcases hNumR_filtered with hNumR_1 | hNumR_pq
  · right; right; exact normal_of_card_one r hNumR_1

  -- Step 6: With `n_r = p*q`, filter `n_q`; if `n_q = 1`, finish.
  -- Step 6.1: Since `n_q | p*r`, the only candidates are `1`, `p`, `r`, and `p*r`.
  have hNumQ_options := dvd_prime_mul_options hp_prime hr_prime hpr_ne hNumQ_dvd

  -- Step 6.2: Exclude `n_q = p`, because `p < q` prevents `p ≡ 1 mod q`.
  have hp_not_one_mod_q : ¬ (p ≡ 1 [MOD q]) := by
    intro h
    have h1_le : 1 ≤ p := by omega
    have hdvd : q ∣ p - 1 := (Nat.modEq_iff_dvd' h1_le).mp h.symm
    by_cases hzero : p - 1 = 0
    · omega
    · have := Nat.le_of_dvd (Nat.pos_of_ne_zero hzero) hdvd; omega

  -- Step 6.3: Filter `n_q` down to `1`, `r`, or `p*r`.
  have hNumQ_filtered : Nat.card (Sylow q G) = 1 ∨ Nat.card (Sylow q G) = r ∨ Nat.card (Sylow q G) = p * r := by
    rcases hNumQ_options with h1 | hp' | hr' | hpr'
    · left; exact h1
    · exfalso; exact hp_not_one_mod_q (hp' ▸ hNumQ_mod)
    · right; left; exact hr'
    · right; right; exact hpr'

  -- Step 6.4: If `n_q = 1`, the Sylow `q`-subgroup is normal and the proof is done.
  rcases hNumQ_filtered with hNumQ_1 | hNumQ_eq_r | hNumQ_eq_pr
  · right; left; exact normal_of_card_one q hNumQ_1

  -- Step 7: Filter `n_p`; if `n_p = 1`, finish.
  -- Step 7.1: Since `n_p | q*r`, the candidates are `1`, `q`, `r`, and `q*r`.
  have hNumP_options := dvd_prime_mul_options hq_prime hr_prime hqr_ne hNumP_dvd

  -- Step 7.2: If `n_p = 1`, the Sylow `p`-subgroup is normal.
  rcases hNumP_options with hNumP_1 | hNumP_eq_q | hNumP_eq_r | hNumP_eq_qr
  · left; exact normal_of_card_one p hNumP_1

  -- Step 8: Eliminate the branches with `n_q = r`.
  · -- Step 8.1: Case `n_p = q`.
    -- Step 8.1.1: From `n_q = r` and `n_q ≡ 1 mod q`, get `q | r - 1`.
    have hr_mod_q : r ≡ 1 [MOD q] := hNumQ_eq_r ▸ hNumQ_mod
    have h1_le_r : 1 ≤ r := by omega
    have hq_dvd_rm1 : q ∣ r - 1 := (Nat.modEq_iff_dvd' h1_le_r).mp hr_mod_q.symm
    -- Step 8.1.2: The divisibility `q | r - 1` and `r > q` give `r ≥ q + 1`.
    have hr_ge_q1 : r ≥ q + 1 := by
      by_cases hzero : r - 1 = 0
      · omega
      · have := Nat.le_of_dvd (Nat.pos_of_ne_zero hzero) hq_dvd_rm1; omega
    exfalso
    -- Step 8.1.3: Record the element-counting inequality that motivates this branch.
    have hint := element_count_exceeds hp_ge_2 hq_ge_3 hr_ge_q1
    have h1_le_p : 1 ≤ p := by omega
    have h1_le_q : 1 ≤ q := by omega
    have h1_le_r' : 1 ≤ r := by omega
    -- Step 8.1.4: Translate `n_r = p*q` and `n_p = q` into modular constraints.
    have hpq_mod_r : p * q ≡ 1 [MOD r] := hNumR_pq ▸ hNumR_mod
    have hq_mod_p : q ≡ 1 [MOD p] := hNumP_eq_q ▸ hNumP_mod
    -- Step 8.1.5: From `q ≡ 1 mod p`, get `p | q - 1` and hence `q ≥ p + 1`.
    have hp_dvd_qm1 : p ∣ q - 1 := by
      have h1_le_q' : 1 ≤ q := by omega
      exact (Nat.modEq_iff_dvd' h1_le_q').mp hq_mod_p.symm
    have hq_ge_p1 : q ≥ p + 1 := by
      by_cases hzero : q - 1 = 0
      · omega
      · have := Nat.le_of_dvd (Nat.pos_of_ne_zero hzero) hp_dvd_qm1; omega
    have helem_exceeds : (p : ℤ) * q * r + (r - 1) * (q - 1) > p * q * r := by
      have h1 : (r - 1 : ℤ) * (q - 1) > 0 := by
        apply mul_pos <;> linarith
      linarith

    -- Step 8.1.6: From `p*q ≡ 1 mod r`, obtain `r | p*q - 1`.
    have h_pq_ge_6 : p * q ≥ 6 := by nlinarith
    have h_pqm1_pos : p * q - 1 > 0 := by omega
    have h1_le_pq : 1 ≤ p * q := by omega
    have hr_dvd_pqm1 : r ∣ p * q - 1 := (Nat.modEq_iff_dvd' h1_le_pq).mp hpq_mod_r.symm
    have hr_le_pqm1 : r ≤ p * q - 1 := Nat.le_of_dvd h_pqm1_pos hr_dvd_pqm1

    -- Step 8.1.7: First rule out `p = 2`.
    have hp_not_2 : p ≠ 2 := by
      intro hp_eq_2
      subst hp_eq_2
      have h2q_m1_eq : 2 * q - 1 = 2 * q - 1 := rfl

      -- Step 8.1.7.1: With `p = 2`, divisibility becomes `r | 2*q - 1`.
      have h2qm1_lt_2r : 2 * q - 1 < 2 * r := by
        omega
      have hr_dvd_2qm1 : r ∣ 2 * q - 1 := hr_dvd_pqm1

      -- Step 8.1.7.2: Split according to whether the divisor is the whole number.
      rcases Nat.eq_or_lt_of_le (Nat.le_of_dvd h_pqm1_pos hr_dvd_2qm1) with h_eq | h_lt
      · -- Step 8.1.7.3: If `r = 2*q - 1`, its residue mod `q` is `q - 1`, not `1`.
        have hr_eq : r = 2 * q - 1 := by omega
        have h_2qm1_mod_q : (2 * q - 1) % q = q - 1 := by
          have hq_pos : 0 < q := hq_prime.pos
          have hq_ge_2 : q ≥ 2 := hq_prime.two_le
          have h_eq' : 2 * q - 1 = q + (q - 1) := by omega
          rw [h_eq']
          rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
          exact Nat.mod_eq_of_lt (by omega : q - 1 < q)
        have hr_mod_q' : r % q = q - 1 := by rw [hr_eq, h_2qm1_mod_q]
        have hr_mod_q'' : r % q = 1 := by
          have := hr_mod_q
          rw [Nat.ModEq] at this
          have hq_ge_2 : q ≥ 2 := hq_prime.two_le
          simp only [Nat.mod_eq_of_lt (by omega : 1 < q)] at this
          exact this
        have hq_eq_2 : q = 2 := by omega
        omega
      · -- Step 8.1.7.4: If `r < 2*q - 1`, then `r = q + 1`, contradicting primality.

        have hr_form : r = q + 1 := by
          have h1_le_r : 1 ≤ r := by omega
          have hq_dvd_rm1 : q ∣ r - 1 := (Nat.modEq_iff_dvd' h1_le_r).mp hr_mod_q.symm
          obtain ⟨k, hk⟩ := hq_dvd_rm1
          have hr_eq : r = 1 + q * k := by omega
          have hk_ge_1 : k ≥ 1 := by
            by_contra hk_zero
            push_neg at hk_zero
            have hk_eq_0 : k = 0 := by omega
            simp [hk_eq_0] at hr_eq
            omega
          have hqk_bound : q * k < 2 * q - 2 := by omega
          have hk_eq_1 : k = 1 := by
            by_contra hk_ne_1
            have hk_ge_2 : k ≥ 2 := by omega
            have : q * k ≥ q * 2 := Nat.mul_le_mul_left q hk_ge_2
            omega
          simp [hk_eq_1] at hr_eq
          omega

        have hq_odd : Odd q := hq_prime.odd_of_ne_two (by omega)
        have hr_even : Even r := by
          rw [hr_form]
          exact Odd.add_one hq_odd
        have hr_eq_2 : r = 2 := by
          have hr_dvd_2 : 2 ∣ r := hr_even.two_dvd
          exact ((hr_prime.eq_one_or_self_of_dvd 2 hr_dvd_2).resolve_left (by norm_num)).symm
        omega

    -- Step 8.1.8: Since `p` is prime and not `2`, we have `p ≥ 3`.
    have hp_ge_3 : p ≥ 3 := by omega

    -- Step 8.1.9: Use `p | q - 1` and primality to sharpen to `q ≥ 2*p + 1`.
    have hq_ge_2p1 : q ≥ 2 * p + 1 := by
      by_contra h_lt
      push_neg at h_lt
      have hq_le_2p : q ≤ 2 * p := by omega
      have hq_form : ∃ m : ℕ, q = 1 + m * p := by
        have hmod := hp_dvd_qm1
        obtain ⟨m, hm⟩ := hmod
        use m
        have hq_pos : q ≥ 1 := by omega
        have h1 : q = 1 + (q - 1) := by omega
        rw [hm, mul_comm] at h1
        exact h1
      obtain ⟨m, hq_eq⟩ := hq_form
      have hm_bound : m * p ≤ 2 * p - 1 := by omega
      have hm_le_1 : m ≤ 1 := by
        by_contra hm_ge_2
        push_neg at hm_ge_2
        have : m * p ≥ 2 * p := Nat.mul_le_mul_right p hm_ge_2
        omega
      interval_cases m
      · -- Step 8.1.9.1: `m = 0` would make `q = 1`.
        simp at hq_eq
        omega
      · -- Step 8.1.9.2: `m = 1` makes `q = p + 1`, an even prime greater than `2`.
        simp at hq_eq
        have hp_odd : Odd p := hp_prime.odd_of_ne_two (by omega)
        have hq_even : Even q := by
          rw [hq_eq]
          have : Even (1 + p) := by rw [Nat.add_comm]; exact Odd.add_one hp_odd
          exact this
        have hq_eq_2 : q = 2 := by
          have hq_dvd_2 : 2 ∣ q := hq_even.two_dvd
          exact ((hq_prime.eq_one_or_self_of_dvd 2 hq_dvd_2).resolve_left (by norm_num)).symm
        omega

    -- Step 8.1.10: The previous bound forces `q ≥ 7`.
    have hq_ge_7 : q ≥ 7 := by omega

    -- Step 8.1.11: Use `q | r - 1` and primality to sharpen to `r ≥ 2*q + 1`.
    have hr_ge_2q1 : r ≥ 2 * q + 1 := by
      by_contra h_lt
      push_neg at h_lt
      have hr_le_2q : r ≤ 2 * q := by omega
      have hr_form : ∃ l : ℕ, r = 1 + l * q := by
        have hmod := hq_dvd_rm1
        obtain ⟨l, hl⟩ := hmod
        use l
        have hr_pos : r ≥ 1 := by omega
        have h1 : r = 1 + (r - 1) := by omega
        rw [hl, mul_comm] at h1
        exact h1
      obtain ⟨l, hr_eq⟩ := hr_form
      have hl_bound : l * q ≤ 2 * q - 1 := by omega
      have hl_le_1 : l ≤ 1 := by
        by_contra hgt
        push_neg at hgt
        have hl_ge_2 : l ≥ 2 := hgt
        have : 2 * q ≤ l * q := Nat.mul_le_mul_right q hl_ge_2
        omega
      interval_cases l
      · -- Step 8.1.11.1: `l = 0` would make `r = 1`.
        simp at hr_eq
        omega
      · -- Step 8.1.11.2: `l = 1` makes `r = q + 1`, an even prime greater than `2`.
        simp at hr_eq
        have hq_odd : Odd q := hq_prime.odd_of_ne_two (by omega)
        have hr_even : Even r := by
          rw [hr_eq]
          have : Even (1 + q) := by rw [Nat.add_comm]; exact Odd.add_one hq_odd
          exact this
        have hr_eq_2 : r = 2 := by
          have hr_dvd_2 : 2 ∣ r := hr_even.two_dvd
          exact ((hr_prime.eq_one_or_self_of_dvd 2 hr_dvd_2).resolve_left (by norm_num)).symm
        omega

    -- Step 8.1.12: Finish by splitting on the remaining smallest prime case `p = 3`.
    by_cases hp_eq_3 : p = 3
    · -- Step 8.1.12.1: If `p = 3`, use `r | 3*q - 1` and `r ≥ 2*q + 1`.
      subst hp_eq_3

      have h3q_m1_eq : 3 * q - 1 = 3 * q - 1 := rfl
      have hr_dvd_3qm1 : r ∣ 3 * q - 1 := hr_dvd_pqm1
      have h3qm1_pos : 3 * q - 1 > 0 := by omega
      have hr_le_3qm1 : r ≤ 3 * q - 1 := Nat.le_of_dvd h3qm1_pos hr_dvd_3qm1

      rcases Nat.eq_or_lt_of_le hr_le_3qm1 with hr_eq_3qm1 | hr_lt_3qm1
      · -- Step 8.1.12.2: If `r = 3*q - 1`, its residue mod `q` is `q - 1`.
        have hr_mod_q' : r % q = q - 1 := by
          have hq_pos : 0 < q := hq_prime.pos
          have hq_ge_2 : q ≥ 2 := hq_prime.two_le
          have h_eq' : 3 * q - 1 = 2 * q + (q - 1) := by omega
          have hr_eq' : r = 2 * q + (q - 1) := by omega
          have h2q_mod : (2 * q) % q = 0 := by rw [Nat.mul_mod_left]
          rw [hr_eq', Nat.add_mod, h2q_mod, Nat.zero_add, Nat.mod_mod]
          exact Nat.mod_eq_of_lt (by omega : q - 1 < q)
        have hr_mod_q'' : r % q = 1 := by
          have := hr_mod_q
          rw [Nat.ModEq] at this
          have hq_ge_2 : q ≥ 2 := hq_prime.two_le
          simp only [Nat.mod_eq_of_lt (by omega : 1 < q)] at this
          exact this
        omega
      · -- Step 8.1.12.3: If `r < 3*q - 1`, divisibility bounds `r` by half.
        have hr_le_half : r ≤ (3 * q - 1) / 2 := by
          have h : r * 2 ≤ 3 * q - 1 := by
            have hr_dvd' := hr_dvd_3qm1
            have hr_lt' := hr_lt_3qm1
            obtain ⟨k, hk⟩ := hr_dvd'
            have hk_ge_2 : k ≥ 2 := by
              by_contra hk_lt
              push_neg at hk_lt
              have hk_le_1 : k ≤ 1 := by omega
              interval_cases k
              · -- Step 8.1.12.4: `k = 0` makes `3*q - 1 = 0`.
                simp at hk; omega
              · -- Step 8.1.12.5: `k = 1` contradicts the strict case `r < 3*q - 1`.
                have hr_eq : r = 3 * q - 1 := by omega
                omega
            have h3qm1_eq : r * k = 3 * q - 1 := by omega
            calc r * 2 ≤ r * k := Nat.mul_le_mul_left r hk_ge_2
              _ = 3 * q - 1 := h3qm1_eq
          omega
        have h_half_lt : (3 * q - 1) / 2 < 2 * q + 1 := by omega
        omega

    · -- Step 8.1.13: If `p ≠ 3`, then `p ≥ 5`; squeeze the divisor quotient.
      have hp_ge_5 : p ≥ 5 := by
        have hp_odd := hp_prime.odd_of_ne_two (by omega)
        by_contra h_lt
        push_neg at h_lt
        have hp_le_4 : p ≤ 4 := by omega
        have hp_eq_3_or_4 : p = 3 ∨ p = 4 := by omega
        rcases hp_eq_3_or_4 with hp3 | hp4
        · exact hp_eq_3 hp3
        · subst hp4
          have h4_not_prime : ¬ Nat.Prime 4 := by decide
          exact h4_not_prime hp_prime

      -- Step 8.1.13.1: Write `p*q - 1 = k*r`.
      obtain ⟨k, hk⟩ := hr_dvd_pqm1
      have hpqm1_eq_kr : p * q - 1 = k * r := by linarith [hk, mul_comm r k]
      have hk_pos : k ≥ 1 := by
        by_contra hk_zero
        push_neg at hk_zero
        have hk_eq_0 : k = 0 := by omega
        simp [hk_eq_0] at hpqm1_eq_kr
        omega

      -- Step 8.1.13.2: Reduce the equation modulo `q` to get `k % q = q - 1`.
      have hk_mod_q : k % q = q - 1 := by
        have hq_pos : 0 < q := hq_prime.pos
        have hq_ge_2 : q ≥ 2 := hq_prime.two_le
        have hp_pos : 0 < p := by omega
        have hpqm1_mod : (p * q - 1) % q = q - 1 := by
          have hpq_mod : (p * q) % q = 0 := Nat.mul_mod_left p q
          have hpq_pos : 0 < p * q := Nat.mul_pos hp_pos hq_pos
          have h1 : p * q - 1 < p * q := Nat.sub_lt hpq_pos (by norm_num)
          have h2 : p * q - 1 ≥ q - 1 := by
            have : p * q ≥ q := Nat.le_mul_of_pos_left q hp_pos
            omega
          have h3 : p * q - 1 = (p - 1) * q + (q - 1) := by
            have hp_ge_1 : p ≥ 1 := by omega
            have hq_ge_1 : q ≥ 1 := by omega
            calc p * q - 1 = p * q - 1 := rfl
              _ = (p - 1 + 1) * q - 1 := by rw [Nat.sub_add_cancel hp_ge_1]
              _ = (p - 1) * q + q - 1 := by ring_nf
              _ = (p - 1) * q + (q - 1) := by omega
          rw [h3]
          rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod]
          exact Nat.mod_eq_of_lt (by omega : q - 1 < q)
        have hkr_mod : (k * r) % q = q - 1 := by
          rw [← hpqm1_eq_kr]; exact hpqm1_mod
        have hr_mod' : r % q = 1 % q := hr_mod_q
        have h1_mod : 1 % q = 1 := Nat.mod_eq_of_lt (by omega : 1 < q)
        have hr_mod'' : r % q = 1 := by rw [hr_mod', h1_mod]
        have hkr_mod' : (k * r) % q = k % q := by
          calc (k * r) % q = (k % q * (r % q)) % q := Nat.mul_mod k r q
            _ = (k % q * 1) % q := by rw [hr_mod'']
            _ = (k % q) % q := by ring_nf
            _ = k % q := Nat.mod_mod _ _
        rw [hkr_mod'] at hkr_mod
        exact hkr_mod

      -- Step 8.1.13.3: The residue condition forces `k ≥ q - 1`.
      have hk_ge_qm1 : k ≥ q - 1 := by
        have hq_pos : 0 < q := hq_prime.pos
        have hmod := hk_mod_q
        by_contra h_lt
        push_neg at h_lt
        have hk_lt_q : k < q := by omega
        have h : k % q = k := Nat.mod_eq_of_lt hk_lt_q
        rw [h] at hmod
        omega

      -- Step 8.1.13.4: Therefore `r = (p*q - 1)/k ≤ (p*q - 1)/(q - 1)`.
      have hr_le : r ≤ (p * q - 1) / (q - 1) := by
        have hk_pos' : 0 < k := by omega
        have hqm1_pos : 0 < q - 1 := by omega
        have h1 : r = (p * q - 1) / k := by
          have hdvd : k ∣ p * q - 1 := ⟨r, hpqm1_eq_kr⟩
          have heq : p * q - 1 = k * r := hpqm1_eq_kr
          have : (p * q - 1) / k = r := by
            rw [heq]
            exact Nat.mul_div_cancel_left r hk_pos'
          exact this.symm
        rw [h1]
        apply Nat.div_le_div_left hk_ge_qm1 hqm1_pos

      -- Step 8.1.13.5: Since `q > p`, the latter quotient is exactly `p`.
      have hpqm1_div : (p * q - 1) / (q - 1) = p := by
        have hq_gt_p : q > p := hpq
        have hqm1_pos : 0 < q - 1 := by omega
        have hp_ge_1 : p ≥ 1 := by omega
        have hq_ge_1 : q ≥ 1 := by omega
        have hdiv_eq : (p * q - 1) = p * (q - 1) + (p - 1) := by
          calc p * q - 1 = p * q - 1 := rfl
            _ = p * (q - 1 + 1) - 1 := by rw [Nat.sub_add_cancel hq_ge_1]
            _ = p * (q - 1) + p - 1 := by ring_nf
            _ = p * (q - 1) + (p - 1) := by omega
        rw [hdiv_eq]
        have hrem_lt : p - 1 < q - 1 := by omega
        rw [mul_comm p (q - 1)]
        rw [Nat.mul_add_div hqm1_pos]
        simp only [Nat.div_eq_of_lt hrem_lt, add_zero]

      -- Step 8.1.13.6: This gives `r ≤ p`, contradicting `p < q < r`.
      omega

  · -- Step 8.2: Case `n_p = r`; reuse the same congruence squeeze.
    exfalso
    -- Step 8.2.1: Convert `n_q = r` and `n_r = p*q` into congruences.
    have hr_mod_q : r ≡ 1 [MOD q] := hNumQ_eq_r ▸ hNumQ_mod
    have hpq_mod_r : p * q ≡ 1 [MOD r] := hNumR_pq ▸ hNumR_mod
    -- Step 8.2.2: From `p*q ≡ 1 mod r`, write `p*q - 1 = k*r`.
    have hpq_ge_6 : p * q ≥ 6 := Nat.mul_le_mul hp_ge_2 hq_ge_3
    have h1_le_pq : 1 ≤ p * q := by omega
    have hr_dvd_pqm1 : r ∣ p * q - 1 := (Nat.modEq_iff_dvd' h1_le_pq).mp hpq_mod_r.symm
    obtain ⟨k, hk⟩ := hr_dvd_pqm1
    have hpqm1_eq_kr : p * q - 1 = k * r := by linarith [hk, mul_comm r k]
    have hk_pos : k ≥ 1 := by
      by_contra hk_zero; push_neg at hk_zero
      have hk_eq_0 : k = 0 := by omega
      simp only [hk_eq_0, zero_mul] at hpqm1_eq_kr
      have hsub : p * q - 1 + 1 = p * q := Nat.sub_add_cancel h1_le_pq
      rw [hpqm1_eq_kr, zero_add] at hsub
      omega
    -- Step 8.2.3: Reduce `k*r = p*q - 1` modulo `q`; since `r ≡ 1 mod q`, get `k % q = q - 1`.
    have hk_mod_q : k % q = q - 1 := by
      have hpqm1_mod : (p * q - 1) % q = q - 1 := by
        have h3 : p * q - 1 = (p - 1) * q + (q - 1) := by
          have hp_ge_1 : p ≥ 1 := by omega
          have hq_ge_1 : q ≥ 1 := by omega
          calc p * q - 1 = (p - 1 + 1) * q - 1 := by rw [Nat.sub_add_cancel hp_ge_1]
            _ = (p - 1) * q + q - 1 := by ring_nf
            _ = (p - 1) * q + (q - 1) := by omega
        rw [h3, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod]
        exact Nat.mod_eq_of_lt (by omega : q - 1 < q)
      have hkr_mod : (k * r) % q = q - 1 := by rw [← hpqm1_eq_kr]; exact hpqm1_mod
      have hr_mod'' : r % q = 1 := by
        rw [Nat.ModEq] at hr_mod_q; simp only [Nat.mod_eq_of_lt (by omega : 1 < q)] at hr_mod_q
        exact hr_mod_q
      have hkr_mod' : (k * r) % q = k % q := by
        calc (k * r) % q = (k % q * (r % q)) % q := Nat.mul_mod k r q
          _ = (k % q * 1) % q := by rw [hr_mod'']
          _ = k % q := by ring_nf; exact Nat.mod_mod _ _
      rw [hkr_mod'] at hkr_mod; exact hkr_mod
    -- Step 8.2.4: Hence `k ≥ q - 1`.
    have hk_ge_qm1 : k ≥ q - 1 := by
      by_contra h_lt; push_neg at h_lt
      have hk_lt_q : k < q := by omega
      have h : k % q = k := Nat.mod_eq_of_lt hk_lt_q
      rw [h] at hk_mod_q; omega
    -- Step 8.2.5: Bound `r` by the quotient `(p*q - 1)/(q - 1)`.
    have hqm1_pos : 0 < q - 1 := by omega
    have hr_le : r ≤ (p * q - 1) / (q - 1) := by
      have hk_pos' : 0 < k := by omega
      have h1 : r = (p * q - 1) / k := by
        have heq : p * q - 1 = k * r := hpqm1_eq_kr
        have : (p * q - 1) / k = r := by rw [heq]; exact Nat.mul_div_cancel_left r hk_pos'
        exact this.symm
      rw [h1]; apply Nat.div_le_div_left hk_ge_qm1 hqm1_pos
    -- Step 8.2.6: Compute that quotient as `p`, contradicting `p < q < r`.
    have hpqm1_div : (p * q - 1) / (q - 1) = p := by
      have hp_ge_1 : p ≥ 1 := by omega
      have hq_ge_1 : q ≥ 1 := by omega
      have hdiv_eq : (p * q - 1) = p * (q - 1) + (p - 1) := by
        calc p * q - 1 = p * (q - 1 + 1) - 1 := by rw [Nat.sub_add_cancel hq_ge_1]
          _ = p * (q - 1) + p - 1 := by ring_nf
          _ = p * (q - 1) + (p - 1) := by omega
      rw [hdiv_eq]; have hrem_lt : p - 1 < q - 1 := by omega
      rw [mul_comm p (q - 1), Nat.mul_add_div hqm1_pos]
      simp only [Nat.div_eq_of_lt hrem_lt, add_zero]
    rw [hpqm1_div] at hr_le; omega

  · -- Step 8.3: Case `n_p = q*r`; reuse the same congruence squeeze.
    exfalso
    -- Step 8.3.1: The same two Sylow congruences as in Step 8.2 are available.
    have hr_mod_q : r ≡ 1 [MOD q] := hNumQ_eq_r ▸ hNumQ_mod
    have hpq_mod_r : p * q ≡ 1 [MOD r] := hNumR_pq ▸ hNumR_mod
    -- Step 8.3.2: Write `p*q - 1 = k*r`.
    have hpq_ge_6 : p * q ≥ 6 := Nat.mul_le_mul hp_ge_2 hq_ge_3
    have h1_le_pq : 1 ≤ p * q := by omega
    have hr_dvd_pqm1 : r ∣ p * q - 1 := (Nat.modEq_iff_dvd' h1_le_pq).mp hpq_mod_r.symm
    obtain ⟨k, hk⟩ := hr_dvd_pqm1
    have hpqm1_eq_kr : p * q - 1 = k * r := by linarith [hk, mul_comm r k]
    have hk_pos : k ≥ 1 := by
      by_contra hk_zero; push_neg at hk_zero
      have hk_eq_0 : k = 0 := by omega
      simp only [hk_eq_0, zero_mul] at hpqm1_eq_kr
      have hsub : p * q - 1 + 1 = p * q := Nat.sub_add_cancel h1_le_pq
      rw [hpqm1_eq_kr, zero_add] at hsub
      omega
    -- Step 8.3.3: Reduce modulo `q` to get `k % q = q - 1`.
    have hk_mod_q : k % q = q - 1 := by
      have hpqm1_mod : (p * q - 1) % q = q - 1 := by
        have h3 : p * q - 1 = (p - 1) * q + (q - 1) := by
          have hp_ge_1 : p ≥ 1 := by omega
          have hq_ge_1 : q ≥ 1 := by omega
          calc p * q - 1 = (p - 1 + 1) * q - 1 := by rw [Nat.sub_add_cancel hp_ge_1]
            _ = (p - 1) * q + q - 1 := by ring_nf
            _ = (p - 1) * q + (q - 1) := by omega
        rw [h3, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod]
        exact Nat.mod_eq_of_lt (by omega : q - 1 < q)
      have hkr_mod : (k * r) % q = q - 1 := by rw [← hpqm1_eq_kr]; exact hpqm1_mod
      have hr_mod'' : r % q = 1 := by
        rw [Nat.ModEq] at hr_mod_q; simp only [Nat.mod_eq_of_lt (by omega : 1 < q)] at hr_mod_q
        exact hr_mod_q
      have hkr_mod' : (k * r) % q = k % q := by
        calc (k * r) % q = (k % q * (r % q)) % q := Nat.mul_mod k r q
          _ = (k % q * 1) % q := by rw [hr_mod'']
          _ = k % q := by ring_nf; exact Nat.mod_mod _ _
      rw [hkr_mod'] at hkr_mod; exact hkr_mod
    -- Step 8.3.4: Again `k ≥ q - 1`, so `r` is at most `(p*q - 1)/(q - 1)`.
    have hk_ge_qm1 : k ≥ q - 1 := by
      by_contra h_lt; push_neg at h_lt
      have hk_lt_q : k < q := by omega
      have h : k % q = k := Nat.mod_eq_of_lt hk_lt_q
      rw [h] at hk_mod_q; omega
    have hqm1_pos : 0 < q - 1 := by omega
    have hr_le : r ≤ (p * q - 1) / (q - 1) := by
      have hk_pos' : 0 < k := by omega
      have h1 : r = (p * q - 1) / k := by
        have heq : p * q - 1 = k * r := hpqm1_eq_kr
        have : (p * q - 1) / k = r := by rw [heq]; exact Nat.mul_div_cancel_left r hk_pos'
        exact this.symm
      rw [h1]; apply Nat.div_le_div_left hk_ge_qm1 hqm1_pos
    -- Step 8.3.5: The quotient equals `p`, contradicting `r > q > p`.
    have hpqm1_div : (p * q - 1) / (q - 1) = p := by
      have hp_ge_1 : p ≥ 1 := by omega
      have hq_ge_1 : q ≥ 1 := by omega
      have hdiv_eq : (p * q - 1) = p * (q - 1) + (p - 1) := by
        calc p * q - 1 = p * (q - 1 + 1) - 1 := by rw [Nat.sub_add_cancel hq_ge_1]
          _ = p * (q - 1) + p - 1 := by ring_nf
          _ = p * (q - 1) + (p - 1) := by omega
      rw [hdiv_eq]; have hrem_lt : p - 1 < q - 1 := by omega
      rw [mul_comm p (q - 1), Nat.mul_add_div hqm1_pos]
      simp only [Nat.div_eq_of_lt hrem_lt, add_zero]
    rw [hpqm1_div] at hr_le; omega

  -- Step 9: The remaining branches have `n_q = p*r`; split by size of `q`.
  all_goals {
    exfalso

    -- Step 9.0.1: Convert the remaining Sylow-number assumptions into congruences.
    have hpr_mod_q : p * r ≡ 1 [MOD q] := hNumQ_eq_pr ▸ hNumQ_mod
    have hpq_mod_r : p * q ≡ 1 [MOD r] := hNumR_pq ▸ hNumR_mod

    -- Step 9.0.2: Turn `p*q ≡ 1 mod r` into `r | p*q - 1`.
    have hpq_ge_6 : p * q ≥ 6 := Nat.mul_le_mul hp_ge_2 hq_ge_3
    have h1_le_pq : 1 ≤ p * q := by omega
    have hr_dvd_pqm1 : r ∣ p * q - 1 := (Nat.modEq_iff_dvd' h1_le_pq).mp hpq_mod_r.symm

    -- Step 9.0.3: Turn `p*r ≡ 1 mod q` into `q | p*r - 1`.
    have hpr_ge_4 : p * r ≥ 4 := by
      have h1 : p * r ≥ 2 * r := Nat.mul_le_mul_right r hp_ge_2
      have h2 : r > q := hqr
      have h3 : q ≥ 3 := hq_ge_3
      omega
    have h1_le_pr : 1 ≤ p * r := by omega
    have hq_dvd_prm1 : q ∣ p * r - 1 := (Nat.modEq_iff_dvd' h1_le_pr).mp hpr_mod_q.symm

    -- Step 9.0.4: Extract the basic size bounds supplied by those divisibilities.
    have h_pqm1_pos : p * q - 1 > 0 := by omega
    have hr_le_pqm1 : r ≤ p * q - 1 := Nat.le_of_dvd h_pqm1_pos hr_dvd_pqm1

    have h_prm1_pos : p * r - 1 > 0 := by omega
    have hq_le_prm1 : q ≤ p * r - 1 := Nat.le_of_dvd h_prm1_pos hq_dvd_prm1

    -- Step 9.0.5: Record lower bounds needed by the final counting estimate.
    have hr_ge_q1 : r ≥ q + 1 := by omega
    have hr_ge_4 : r ≥ 4 := by omega
    have hpr_ge_8 : p * r ≥ 8 := by
      calc p * r ≥ 2 * r := Nat.mul_le_mul_right r hp_ge_2
        _ ≥ 2 * 4 := Nat.mul_le_mul_left 2 hr_ge_4
        _ = 8 := by norm_num
    have hqm1_ge_2 : q - 1 ≥ 2 := by omega
    have hprm1_ge_7 : p * r - 1 ≥ 7 := by omega
    have hprod_ge_14 : (q - 1) * (p * r - 1) ≥ 14 := by
      calc (q - 1) * (p * r - 1) ≥ 2 * 7 := Nat.mul_le_mul hqm1_ge_2 hprm1_ge_7
        _ = 14 := by norm_num

    -- Step 9.0.6: Rephrase the group-cardinality hypothesis in the direction used later.
    have hpqr_eq : p * q * r = Fintype.card G := hG.symm

    -- Step 9.0.7: Prove the elementary inequality `q*r > q + r`.
    have hqr_bound : q * r > q + r := by
      have hq3 : q ≥ 3 := hq_ge_3
      have hr4 : r ≥ 4 := by omega
      have hq_le_rm1 : q ≤ r - 1 := by omega
      have hqr_ge_3r : q * r ≥ 3 * r := Nat.mul_le_mul_right r hq3
      have h3r_gt : 3 * r > 2 * r - 1 := by omega
      calc q + r ≤ 2 * r - 1 := by omega
        _ < 3 * r := h3r_gt
        _ ≤ q * r := hqr_ge_3r

    -- Step 9.0.8: Multiply that inequality by `p` to obtain `p*q*r + 1 > p*q + p*r`.
    have h_elem : p * q * r + 1 > p * q + p * r := by
      have h1 : p * (q * r) > p * (q + r) := Nat.mul_lt_mul_of_pos_left hqr_bound (by omega : 0 < p)
      have h2 : p * (q + r) = p * q + p * r := Nat.mul_add p q r
      have h3 : p * (q * r) = p * q * r := by ring
      rw [h2, h3] at h1
      exact Nat.lt_add_one_of_lt h1

    -- Step 9.1: If `q ≥ 2p`, a number-theoretic helper gives the contradiction.
    by_cases hq_2p : q ≥ 2 * p
    ·
      exact nq_pr_case_q_ge_2p hp_prime hq_prime hr_prime hpq hqr hq_2p hr_dvd_pqm1 hq_dvd_prm1
    · -- Step 9.2: If `q < 2p`, element counting gives too many `q`/`r` elements.
      push_neg at hq_2p
      -- Step 9.2.1: Reprove the positive excess inequality in the local branch.
      have h_elem_bound : p * q * r + 1 > p * q + p * r := by
        have hr4 : r ≥ 4 := by omega
        have hqr_gt : q * r > q + r := by
          have h1 : q * r ≥ 3 * r := Nat.mul_le_mul_right r hq_ge_3
          calc q + r ≤ 2 * r - 1 := by omega
            _ < 3 * r := by omega
            _ ≤ q * r := h1
        have h1 : p * (q * r) > p * (q + r) := Nat.mul_lt_mul_of_pos_left hqr_gt hp_prime.pos
        have h2 : p * (q + r) = p * q + p * r := Nat.mul_add p q r
        have h3 : p * (q * r) = p * q * r := by ring
        omega
      -- Step 9.2.2: Prepare the Sylow `r` and `q` representatives used by the count.
      have hG_card : Fintype.card G = p * q * r := hG
      let Rg : Sylow r G := default
      let Qg : Sylow q G := default
      -- Step 9.2.3: Compute the order of the representative Sylow `r`-subgroup.
      have hCardRg : Fintype.card Rg = r := by
        have h := Sylow.card_eq_multiplicity (G := G) (p := r) Rg
        simp only [Nat.card_eq_fintype_card] at h
        have hFactor : Nat.factorization (Fintype.card G) r = 1 := by
          rw [hG]
          have hpr_ne' : p ≠ r := Nat.ne_of_lt (Nat.lt_trans hpq hqr)
          have hqr_ne' : q ≠ r := Nat.ne_of_lt hqr
          exact factorization_pqr_at_r hp_prime hq_prime hr_prime hpr_ne' hqr_ne'
        rw [h, hFactor, pow_one]
      -- Step 9.2.4: Compute the order of the representative Sylow `q`-subgroup.
      have hCardQg : Fintype.card Qg = q := by
        have h := Sylow.card_eq_multiplicity (G := G) (p := q) Qg
        simp only [Nat.card_eq_fintype_card] at h
        have hFactor : Nat.factorization (Fintype.card G) q = 1 := by
          rw [hG]
          have hpq_ne' : p ≠ q := Nat.ne_of_lt hpq
          have hqr_ne' : q ≠ r := Nat.ne_of_lt hqr
          exact factorization_pqr_at_q hp_prime hq_prime hr_prime hpq_ne' hqr_ne'
        rw [h, hFactor, pow_one]
      -- Step 9.2.5: Name the two Sylow-number equalities needed by the counting helper.
      have hNumRg : Nat.card (Sylow r G) = p * q := hNumR_pq
      have hNumQg : Nat.card (Sylow q G) = p * r := hNumQ_eq_pr
      -- Step 9.3: The arithmetic bound says the counted elements exceed `|G|`.
      have h_elem_gt : 2 * p * q * r - p * q - p * r + 1 > p * q * r := by
        have h : p * q + p * r < p * q * r + 1 := h_elem_bound
        have h2 : p * q + p * r ≤ p * q * r := Nat.lt_succ_iff.mp h
        have h3 : p * q * r + p * q * r ≥ p * q + p * r + p * q * r := by omega
        have h4 : 2 * p * q * r = p * q * r + p * q * r := by ring
        omega
      exfalso
      -- Step 9.4: The element-counting helper gives the opposite inequality.
      have h_elem_le_G : 2 * p * q * r - p * q - p * r + 1 ≤ p * q * r := by
        exact elem_count_bound_final' p q r hpq hqr hG hNumQg hNumRg
      omega
  }
