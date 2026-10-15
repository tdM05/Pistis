import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Use Cauchy's Theorem and induction to show that a finite abelian group has a subgroup of order $n$ for each positive divisor $n$ of its order.
-/

/-Informal Proof

Let $G$ be a finite abelian group. We use induction on $|G|$. Certainly the result holds for the trivial group. And if $|G|=p$ for some prime $p$, then the positive divisors of $|G|$ are 1 and $p$ and the result is again trivial.

Now assume that the statement is true for all groups of order strictly smaller than $|G|$, and let $n$ be a positive divisor of $|G|$ with $n>1$. First, if $n$ is prime then Cauchy's Theorem allows us to find an element $x \in G$ having order $n$. Then $\langle x\rangle$ is the desired subgroup. On the other hand, if $n$ is not prime, then $n$ has a prime divisor $p$, so that $n=k p$ for some integer $k$. Cauchy's Theorem allows us to find an element $x$ having order $p$. Set $N=\langle x\rangle$. By Lagrange's Theorem,
$$
|G / N|=\frac{|G|}{|N|}<|G| .
$$
Now, by the inductive hypothesis, the group $G / N$ must have a subgroup of order $k$. And by the Lattice Isomorphism Theorem, this subgroup has the form $H / N$ for some subgroup $H$ of $G$. Then $|H|=k|N|=k p=n$, so that $H$ has order $n$. This completes the inductive step.
-/

/-
  Step 1: This theorem states that for a finite abelian group G, if n divides |G|,
          then there exists a subgroup H of G with |H| = n.

  Step 2: The key insight is that for abelian groups, we can prove this by strong induction
          on card G. For n = 1, we use the trivial subgroup. For n > 1, we find a prime p
          dividing n, use Cauchy/Sylow to get a subgroup N of order p, then apply
          the inductive hypothesis to the quotient G/N to get a subgroup K' of order n/p.
          The preimage of K' under the quotient map has order n.
-/
theorem Dummit_Foote_exercise_3_4_4 {G : Type*} [CommGroup G] [Fintype G] {n : ℕ}
    (hn : n ∣ (card G)) :
    ∃ (H : Subgroup G) (H_fin : Fintype H), @card H H_fin = n  := by
  -- Step 1: Use strong induction on the cardinality of G.
  revert n hn
  -- Step 2: Strong induction on card G.
  induction' hG_ind : card G using Nat.strongRecOn with m ih generalizing G
  intro n hn
  -- Step 2.1: Since hG_ind : card G = m, we can rewrite hn to use card G.
  have hn' : n ∣ card G := by rw [hG_ind]; exact hn
  -- Step 3: Handle the case n = 0.
  -- If n = 0 and n | card G, then card G = 0. But card G ≥ 1, contradiction.
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · exfalso
    have hcard_pos : 0 < card G := Fintype.card_pos
    have : card G = 0 := Nat.eq_zero_of_zero_dvd hn'
    omega
  -- Step 4: Handle the case n = 1.
  rcases eq_or_ne n 1 with rfl | hn_ne_one
  · refine ⟨⊥, inferInstance, ?_⟩
    have : Nat.card (⊥ : Subgroup G) = 1 := Subgroup.card_bot
    rw [Nat.card_eq_fintype_card] at this
    exact this
  -- Step 5: n > 1, so n has a prime divisor p.
  have hn_gt_one : 1 < n := by omega
  obtain ⟨p, hp_prime, hp_dvd_n⟩ := Nat.exists_prime_and_dvd hn_ne_one
  -- Step 6: p | card G since p | n and n | card G.
  have hp_dvd_card : p ∣ card G := dvd_trans hp_dvd_n hn'
  -- Step 7: Get k such that n = p * k.
  obtain ⟨k, hk_eq⟩ := hp_dvd_n
  have hp_pos : 0 < p := hp_prime.pos
  -- Step 8: Use Sylow's theorem to get a subgroup N of order p.
  haveI : Fact (Nat.Prime p) := ⟨hp_prime⟩
  have hp_pow_one_dvd : p ^ 1 ∣ Nat.card G := by
    simp only [pow_one, Nat.card_eq_fintype_card]
    exact hp_dvd_card
  obtain ⟨N, hN_card_nat⟩ := Sylow.exists_subgroup_card_pow_prime p hp_pow_one_dvd
  simp only [pow_one] at hN_card_nat
  -- Step 9: N has cardinality p.
  haveI hN_fintype : Fintype N := Fintype.ofFinite N
  have hN_card : card N = p := by
    rw [← Nat.card_eq_fintype_card]
    exact hN_card_nat
  -- Step 10: N is normal since G is abelian.
  haveI hN_normal : N.Normal := N.normal_of_comm
  -- Step 10.1: G/N is finite since G is finite and N is a normal subgroup.
  classical
  haveI : Fintype (G ⧸ N) := Quotient.fintype (QuotientGroup.leftRel N)
  -- Step 11: The quotient G/N has cardinality card G / p.
  -- We need to show that k | card (G/N) and then apply IH to G/N.
  -- But the IH is on card G, so we need card (G/N) < card G.
  have hN_card_pos : 0 < card N := by rw [hN_card]; exact hp_pos
  have hcard_quot : card (G ⧸ N) * card N = card G := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    simp only [Nat.card_eq_fintype_card] at h
    exact h.symm
  have hcard_quot' : card (G ⧸ N) = card G / p := by
    have h : card G = card (G ⧸ N) * p := by rw [← hN_card]; exact hcard_quot.symm
    have h2 : card G / p = card (G ⧸ N) * p / p := congrArg (· / p) h
    rw [h2]
    have h3 : card (G ⧸ N) * p / p = card (G ⧸ N) := Nat.mul_div_cancel _ hp_pos
    exact h3.symm
  -- Step 12: card (G/N) < card G since p > 1.
  have hcard_quot_lt : card (G ⧸ N) < card G := by
    rw [hcard_quot']
    have hp_gt_one : 1 < p := hp_prime.one_lt
    have hG_pos : 0 < card G := Fintype.card_pos
    exact Nat.div_lt_self hG_pos hp_gt_one
  -- Step 13: k | card (G/N).
  have hk_dvd_quot : k ∣ card (G ⧸ N) := by
    rw [hcard_quot']
    have hn_dvd : p * k ∣ card G := by rw [← hk_eq]; exact hn'
    have hp_ne_zero : p ≠ 0 := hp_pos.ne'
    -- We want k | (card G / p). Since p * k | card G, we have k | card G / p.
    have : k ∣ card G / p := by
      rcases hn_dvd with ⟨c, hc⟩
      use c
      calc card G / p = p * k * c / p := by rw [hc]
        _ = p * (k * c) / p := by ring_nf
        _ = k * c := Nat.mul_div_cancel_left _ hp_pos
    exact this
  -- Step 14: k > 0 since n = p * k and n > 0.
  have hk_pos : 0 < k := by
    by_contra hk_not_pos
    push_neg at hk_not_pos
    interval_cases k
    simp only [mul_zero] at hk_eq
    omega
  -- Step 15: G/N is a commutative group (automatically inferred from CommGroup G).
  -- Step 16: Apply IH to G/N to get a subgroup K' of order k.
  rw [hG_ind] at hcard_quot_lt
  -- ih signature: (m' : ℕ) → m' < m → {G' : Type*} → [CommGroup G'] → [Fintype G']
  --               → card G' = m' → {n : ℕ} → n ∣ m' → ∃ H H_fin, card H = n
  have hih := @ih (card (G ⧸ N)) hcard_quot_lt (G ⧸ N) _ _ rfl k hk_dvd_quot
  obtain ⟨K', hK'_fin, hK'_card⟩ := hih
  -- Step 17: Get the preimage H of K' under the quotient map.
  let H : Subgroup G := K'.comap (QuotientGroup.mk' N)
  -- Step 18: H contains N (since ker(mk' N) = N and 1 ∈ K').
  have hN_le_H : N ≤ H := by
    intro x hx
    show x ∈ K'.comap (QuotientGroup.mk' N)
    rw [Subgroup.mem_comap]
    have h_eq_one : (QuotientGroup.mk' N) x = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hx
    rw [h_eq_one]
    exact K'.one_mem
  -- Step 19: Compute card H using the index formula.
  -- We use: card H * H.index = card G, H.index = K'.index (since mk' N is surjective),
  -- and card K' * K'.index = card (G/N), card (G/N) * card N = card G.
  haveI hH_fintype : Fintype H := Fintype.ofFinite H
  have hH_card : card H = n := by
    -- card H * H.index = card G (Lagrange's theorem)
    have h1 : card H * H.index = card G := by
      have := Subgroup.card_mul_index H
      simp only [Nat.card_eq_fintype_card] at this
      exact this
    -- H.index = K'.index because mk' N is surjective
    have h2 : H.index = K'.index := by
      have hsurj := QuotientGroup.mk'_surjective N
      exact Subgroup.index_comap_of_surjective K' hsurj
    -- card K' * K'.index = card (G/N) (Lagrange's theorem in G/N)
    have h3 : card K' * K'.index = card (G ⧸ N) := by
      have := Subgroup.card_mul_index K'
      simp only [Nat.card_eq_fintype_card] at this
      exact this
    -- Combine: card H * K'.index = card G = card K' * K'.index * card N
    rw [h2] at h1
    have h5 : card G = card K' * K'.index * card N := by
      calc card G = card (G ⧸ N) * card N := hcard_quot.symm
        _ = card K' * K'.index * card N := by rw [h3]
    rw [h5] at h1
    -- h1: card H * K'.index = card K' * K'.index * card N
    have hindex_pos : 0 < K'.index := by
      have h := Subgroup.index_ne_zero_of_finite (H := K')
      omega
    -- Rewrite to get card H * K'.index = card K' * card N * K'.index
    have h6 : card K' * K'.index * card N = card K' * card N * K'.index := by ring
    rw [h6] at h1
    have hH_eq : card H = card K' * card N := Nat.eq_of_mul_eq_mul_right hindex_pos h1
    rw [hH_eq, hK'_card, hN_card, hk_eq, mul_comm]
  -- Step 20: Return H.
  exact ⟨H, hH_fintype, hH_card⟩
