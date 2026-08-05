import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

Prove that a group of order $p^2$, $p$ a prime, has a normal subgroup of order $p$.
-/

/-Informal Proof

We use the result from problem 40 which is as follows: Suppose $G$ is a group, $H$ is a subgroup and $|G|=n$ and $n \nmid\left(i_G(H)\right) !$. Then there exists a normal subgroup $K \neq \{ e \}$ and $K \subseteq H$.

So, we have now a group $G$ of order $p^2$. Suppose that the group is cyclic, then it is abelian and any subgroup of order $p$ is normal. Now let us suppose that $G$ is not cyclic, then there exists an element $a$ of order $p$, and $A=\langle a\rangle$. Now $i_G(A)=p$, so $p^2 \nmid p$ ! , hence by the above result there is a normal subgroup $K$, non-trivial and $K \subseteq A$. But $|A|=p$, a prime order subgroup, hence has no non-trivial subgroup, so $K=A$. so $A$ is normal subgroup.
-/

theorem Herstein_exercise_2_5_44 {G : Type*} [Group G] [Fintype G] {p : ℕ}
  (hp : Nat.Prime p) (hG : card G = p^2) :
  ∃ (N : Subgroup G) (Fin : Fintype N), @card N Fin = p ∧ N.Normal := by
  classical
  -- Step 1: Prepare the numerical setting so the `p`-group tools apply smoothly.
  haveI : Fact p.Prime := ⟨hp⟩
  -- Step 1.1: Translate the cardinality assumption into `Nat.card` for `IsPGroup` lemmas.
  have hNatCard : Nat.card G = p ^ 2 := by
    simpa [Nat.card_eq_fintype_card] using hG
  -- Step 1.2: Register that `G` is a `p`-group.
  have hPGroup : IsPGroup p G := IsPGroup.of_card (G:=G) (p:=p) (n:=2) hNatCard
  -- Step 1.3: Prove that `G` has more than one element by bounding `p ^ 2` from below.
  have hp_ge_two : 2 ≤ p := hp.two_le
  -- Step 1.3.1: Compare `p ^ 2` with `4` to obtain a concrete lower bound.
  have hPow_ge : 4 ≤ p ^ 2 := by
    have : 2 * 2 ≤ p * p := Nat.mul_le_mul hp_ge_two hp_ge_two
    simpa [pow_two] using this
  -- Step 1.3.2: Convert the numeric inequality into an inequality about `card G`.
  have hOneLtPow : 1 < p ^ 2 := lt_of_lt_of_le (by decide : 1 < 4) hPow_ge
  have hOneLtCard : 1 < Fintype.card G := by
    simpa [hG] using hOneLtPow
  -- Step 1.4: Turn the strict inequality into a `Nontrivial` instance on `G`.
  haveI : Nontrivial G := (Fintype.one_lt_card_iff_nontrivial).1 hOneLtCard
  -- Step 2: Extract a specific element of the center that is not the identity.
  have hCenterNT : Nontrivial (Subgroup.center G) := hPGroup.center_nontrivial
  -- Step 2.1: Choose a nontrivial central element.
  obtain ⟨⟨z, hz_cent⟩, hz_ne⟩ := exists_ne (1 : Subgroup.center G)
  -- Step 2.2: Reinterpret the nontriviality inside `G`.
  have hz_ne_one : z ≠ (1 : G) := by
    intro hz_eq
    apply hz_ne
    ext
    simp [hz_eq]
  -- Step 3: Record the prime-power order of the chosen central element.
  have hCenterPGroup : IsPGroup p (Subgroup.center G) := hPGroup.to_subgroup (Subgroup.center G)
  -- Step 3.1: Use the `p`-group structure to describe the order of `z`.
  obtain ⟨k, hk_order⟩ :=
    (IsPGroup.iff_orderOf (p:=p) (G:=Subgroup.center G)).1 hCenterPGroup ⟨z, hz_cent⟩
  -- Step 3.2: Move the order statement back to the ambient group.
  have hz_order : orderOf z = p ^ k := by
    simpa [Subgroup.orderOf_mk] using hk_order
  -- Step 3.3: Show that the exponent is positive since `z` is nontrivial.
  have hk_ne_zero : k ≠ 0 := by
    intro hk_zero
    have : orderOf z = 1 := by simpa [hk_zero] using hz_order
    exact hz_ne_one (orderOf_eq_one_iff.mp this)
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_ne_zero
  -- Step 3.4: Rewrite the exponent as a successor to peel off one power of `p`.
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk_ne_zero
  -- Step 3.5: Document how the element order divides the group cardinality.
  have hz_dvd_card : p ^ Nat.succ t ∣ p ^ 2 := by
    have : p ^ Nat.succ t ∣ Fintype.card G := by
      simpa [hz_order] using (orderOf_dvd_card (G:=G) (x:=z))
    simpa [hG] using this
  -- Step 3.6: (Documentation) From the preceding divisibility, the exponent of `p` cannot exceed `2`.
  obtain ⟨t2, ht2_le, ht2_eq⟩ := (Nat.dvd_prime_pow hp).1 hz_dvd_card
  have ht_eq : Nat.succ t = t2 :=
    (Nat.pow_right_injective hp_ge_two) (by simpa [hz_order] using ht2_eq)
  -- Step 4: Build a central element whose order is exactly `p`.
  let y : G := z ^ (p ^ t)
  -- Step 4.1: Verify that the new element stays in the center.
  have hy_center : y ∈ Subgroup.center G := by
    refine (Subgroup.mem_center_iff).2 ?_
    intro g
    have hcomm : Commute g z := (Subgroup.mem_center_iff.mp hz_cent g)
    simpa [y] using (Commute.pow_right hcomm (p ^ t)).eq
  -- Step 4.2: Note the divisibility needed for the gcd computation.
  have hdivPow : p ^ t ∣ orderOf z := by
    have : p ^ t ∣ p ^ Nat.succ t := by
      refine ⟨p, ?_⟩
      simp [Nat.pow_succ, Nat.mul_comm]
    simpa [hz_order] using this
  -- Step 4.3: Collapse the gcd occurring in the order formula.
  have hGCD : Nat.gcd (orderOf z) (p ^ t) = p ^ t := Nat.gcd_eq_right hdivPow
  -- Step 4.4: Compute the order of `y` explicitly.
  have hyPowRaw :=
    orderOf_pow (x := z) (n := p ^ t)
  have hyPow : orderOf y = (p ^ t * p) / p ^ t := by
    simpa [y, hGCD, hz_order, Nat.pow_succ, Nat.mul_comm] using
      hyPowRaw
  have hy_orderOf : orderOf y = p := by
    have hxPos : 0 < p ^ t := Nat.pow_pos (Nat.Prime.pos hp)
    have hxEq : (p ^ t * p) / p ^ t = p :=
      Nat.div_eq_of_eq_mul_left hxPos (by simp [Nat.mul_comm])
    simp [hyPow, hxEq]
  -- Step 5: Package the cyclic subgroup generated by `y`.
  let N : Subgroup G := Subgroup.zpowers y
  -- Step 5.1: Observe that every element of `N` remains central.
  have hN_le_center : N ≤ Subgroup.center G := (Subgroup.zpowers_le).2 hy_center
  -- Step 5.2: Conclude that `N` is normal since conjugation fixes central elements.
  have hN_normal : N.Normal := by
    refine ⟨?_⟩
    intro n hn g
    have hn_center : n ∈ Subgroup.center G := hN_le_center hn
    have hcomm : g * n = n * g := (Subgroup.mem_center_iff.mp hn_center g)
    have hconj : g * n * g⁻¹ = n := by
      calc
        g * n * g⁻¹ = (n * g) * g⁻¹ := by simp [hcomm]
        _ = n * (g * g⁻¹) := by simp [mul_assoc]
        _ = n := by simp
    simpa [hconj] using hn
  -- Step 5.3: Read off the cardinality of `N` from the order of `y`.
  have cardN : Fintype.card N = p := by
    simpa [N, hy_orderOf] using (Fintype.card_zpowers (x := y))
  -- Step 5.4: Package the subgroup, its finite structure, and normality.
  refine ⟨N, inferInstance, cardN, hN_normal⟩
