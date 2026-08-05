import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that a group of order 312 has a normal Sylow $p$-subgroup for some prime $p$ dividing its order.
-/

/-Informal Proof

Let $n_{13}$ be the number of Sylow 13 -subgroup of $G$. Then by Sylow's Theorem, $n_{13} \equiv 1(\bmod 13)$ and $n_{13}$ divides $2^3 \cdot 3=24$. This implies $n_{13}=1$, so that there is only one Sylow 13 -subgroup, which is consequently normal. The last assertion follows from the fact conjugation preserves the order of a subgroup. So if there is only one subgroup $H$ of order 13 , then for any $g \in G$, we have $\left|g H g^{-1}\right|=|H|=13$, so $g H g^{-1}=H$, i.e. $H$ is normal.
-/

theorem Dummit_Foote_exercise_4_5_14 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 312) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧ P.Normal := by
  -- Step 1: Activate classical logic so that we can select explicit Sylow subgroups.
  classical
  -- Step 2: Confirm that 13 is prime, as required for applying Sylow theory.
  have hprime13 : Nat.Prime 13 := by decide
  -- Step 3: Provide the primality of 13 as an instance for the Sylow API.
  haveI : Fact (Nat.Prime 13) := ⟨hprime13⟩
  -- Step 4: Deduce from the group order that 13 divides |G|.
  have hdiv_card : 13 ∣ card G := by
    -- Step 4.1: Rewrite |G| as 312 and use arithmetic divisibility.
    simp [hG]
  -- Step 5: Choose a specific Sylow 13-subgroup for detailed analysis.
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 13 G))
  -- Step 6: Let n denote the number of Sylow 13-subgroups in G.
  set n : ℕ := Nat.card (Sylow 13 G) with hn
  -- Step 6.1: Record that n is congruent to 1 modulo 13 by Sylow's third theorem.
  have hmod : n ≡ 1 [MOD 13] := by
    -- Step 6.1.1: Specialize the congruence statement to the chosen prime and group.
    simpa [n] using (card_sylow_modEq_one (p := 13) (G := G))
  -- Step 6.2: Note that n is not divisible by 13, again by Sylow's third theorem.
  have hnotdiv : ¬ 13 ∣ n := by
    -- Step 6.2.1: Apply the non-divisibility result and rewrite in terms of n.
    simpa [n] using (not_dvd_card_sylow (p := 13) (G := G))
  -- Step 6.3: Observe that n divides the index of the chosen Sylow subgroup.
  have hdiv_index : n ∣ P.index := by
    -- Step 6.3.1: Use the standard divisor relation between Sylow counts and indices.
    simpa [n] using (Sylow.card_dvd_index (p := 13) (G := G) P)
  -- Step 6.4: The index of P always divides the group order.
  have hindex_dvd : P.index ∣ card G := by
    -- Step 6.4.1: Convert the `Nat.card` formulation into the usual finite cardinals.
    simpa [Nat.card_eq_fintype_card] using (P.1.index_dvd_card)
  -- Step 6.5: Combine the two divisibility facts to see that n divides |G|.
  have hdvd_cardG : n ∣ card G := Nat.dvd_trans hdiv_index hindex_dvd
  -- Step 6.6: Rewrite the preceding statement numerically using |G| = 312.
  have hdvd312 : n ∣ 312 := by
    -- Step 6.6.1: Substitute the given value of |G|.
    simpa [hG] using hdvd_cardG
  -- Step 6.7: Package the coprimality between n and 13 from the non-divisibility.
  have hcoprime : Nat.Coprime n 13 := by
    -- Step 6.7.1: Swap the order after applying the prime coprime criterion.
    simpa [Nat.coprime_comm] using (hprime13.coprime_iff_not_dvd).2 hnotdiv
  -- Step 6.8: Record the factorization 312 = 13 * 24 for later arithmetic manipulation.
  have h312 : 312 = 13 * 24 := by decide
  -- Step 6.9: Use coprimality to improve the divisor information from 312 to 24.
  have hdvd24 : n ∣ 24 := by
    -- Step 6.9.1: First view the divisor relation with 312 as a divisor relation with 13 * 24.
    have hdvdMul : n ∣ 13 * 24 := by
      -- Step 6.9.1.1: Replace 312 with 13 * 24 explicitly.
      simpa [h312] using hdvd312
    -- Step 6.9.2: Cancel the co-prime factor 13 to deduce n ∣ 24.
    exact hcoprime.dvd_of_dvd_mul_left hdvdMul
  -- Step 6.10: Ensure n is positive because there exists at least one Sylow subgroup.
  have hpos : 0 < n := by
    -- Step 6.10.1: The type of Sylow subgroups is nonempty, so its cardinal is positive.
    have : 0 < Nat.card (Sylow 13 G) := Nat.card_pos
    -- Step 6.10.2: Translate this inequality into the notation involving n.
    simpa [n] using this
  -- Step 6.11: Bound n above by 24 using the divisibility information.
  have hle24 : n ≤ 24 := Nat.le_of_dvd (by decide : 0 < 24) hdvd24
  -- Step 6.12: Note that n is at least 1 because it is positive.
  have h1le : 1 ≤ n := Nat.succ_le_of_lt hpos
  -- Step 6.13: Express the congruence as the statement that 13 divides n - 1.
  have hdvdminus : 13 ∣ n - 1 := (Nat.modEq_iff_dvd' h1le).1 hmod.symm
  -- Step 6.14: Introduce an integer k such that n - 1 = 13 * k.
  obtain ⟨k, hk⟩ := hdvdminus
  -- Step 6.15: Rewrite n explicitly in terms of k.
  have hkdef : n = 13 * k + 1 := by
    -- Step 6.15.1: Add 1 back to the equality n - 1 = 13 * k.
    have hSubAdd : (n - 1) + 1 = n := Nat.sub_add_cancel h1le
    calc
      n = (n - 1) + 1 := hSubAdd.symm
      _ = 13 * k + 1 := by simp [hk, add_comm]
  -- Step 6.16: Translate the upper bound on n into an upper bound on 13 * k + 1.
  have hkBound : 13 * k + 1 ≤ 24 := by
    -- Step 6.16.1: Substitute the expression for n obtained above.
    simpa [hkdef] using hle24
  -- Step 6.17: From the previous inequality, obtain a bound on 13 * k.
  have hk_le23 : 13 * k ≤ 23 := by
    -- Step 6.17.1: Work with successor inequalities to remove the +1 shift.
    have hk_succ : Nat.succ (13 * k) ≤ Nat.succ 23 := by
      -- Step 6.17.1.1: Express the inequality in successor form and simplify.
      simpa [Nat.succ_eq_add_one, hkdef] using hkBound
    -- Step 6.17.2: Remove the successor on both sides to recover the desired bound.
    exact (Nat.succ_le_succ_iff).1 hk_succ
  -- Step 6.18: Show that k cannot exceed 1, using the previous bound.
  have hk_le1 : k ≤ 1 := by
    -- Step 6.18.1: Argue by contradiction, assuming k ≥ 2.
    by_contra hk_gt
    -- Step 6.18.2: Turn the negated inequality into the concrete lower bound k ≥ 2.
    have hk_ge2 : 2 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_not_ge hk_gt)
    -- Step 6.18.3: Multiply the inequality by 13 to compare with hk_le23.
    have hk_ge26 : 26 ≤ 13 * k := by
      -- Step 6.18.3.1: Use monotonicity of multiplication by positive naturals.
      have := Nat.mul_le_mul_left 13 hk_ge2
      -- Step 6.18.3.2: Simplify the resulting inequality numerically.
      simpa using this
    -- Step 6.18.4: Combine the lower and upper bounds to reach an impossibility.
    have hk_contra : 26 ≤ 23 := le_trans hk_ge26 hk_le23
    -- Step 6.18.5: Conclude by contradicting the obvious fact that 26 ≰ 23.
    exact (by decide : ¬ 26 ≤ 23) hk_contra
  -- Step 6.19: List the only possible values of k based on the bound k ≤ 1.
  have hk_cases : k = 0 ∨ k = 1 := by
    -- Step 6.19.1: Inspect the value of k directly using the bound k ≤ 1.
    cases hk : k with
    | zero =>
        -- Step 6.19.1.1: The case k = 0 is immediate.
        exact Or.inl rfl
    | succ k' =>
        -- Step 6.19.1.2: Analyze the case k = k' + 1 under the assumption k ≤ 1.
        have hk_succ_le : Nat.succ k' ≤ Nat.succ 0 := by
          -- Step 6.19.1.2.1: Rewrite the inequality using the hypothesis hk_le1.
          simpa [hk, Nat.succ_eq_add_one] using hk_le1
        have hk'_le0 : k' ≤ 0 := (Nat.succ_le_succ_iff).1 hk_succ_le
        -- Step 6.19.1.2.2: Conclude that k' = 0 and therefore k = 1.
        have hk'_zero : k' = 0 := le_antisymm hk'_le0 (Nat.zero_le _)
        exact Or.inr (by simp [hk'_zero])
  -- Step 6.20: Conclude that n itself must be 1 by inspecting the two cases for k.
  have hcardOne : n = 1 := by
    -- Step 6.20.1: Discuss the two possibilities for k.
    cases hk_cases with
    | inl hk0 =>
        -- Step 6.20.1.1: When k = 0, the expression for n immediately yields n = 1.
        simp [hkdef, hk0]
    | inr hk1 =>
        -- Step 6.20.1.2: When k = 1, n would equal 14, contradicting n ∣ 24.
        have : 14 ∣ 24 := by
          -- Step 6.20.1.2.1: Substitute k = 1 into the divisor relation n ∣ 24.
          simp [hkdef, hk1] at hdvd24
        -- Step 6.20.1.2.2: Reach a contradiction because 14 does not divide 24.
        exact False.elim ((by decide : ¬ 14 ∣ 24) this)
  -- Step 6.21: Translate the conclusion back into the language of Sylow subgroups.
  have hcardNat : Nat.card (Sylow 13 G) = 1 := by simpa [n] using hcardOne
  -- Step 6.22: Deduce that the type of Sylow 13-subgroups is a subsingleton.
  have hsubsingleton : Subsingleton (Sylow 13 G) :=
    (Nat.card_eq_one_iff_unique).1 hcardNat |>.1
  -- Step 6.23: Use the subsingleton property to conclude that the chosen Sylow subgroup is normal.
  have hnormal : P.Normal := by
    -- Step 6.23.1: Treat the subsingleton information as an instance.
    letI : Subsingleton (Sylow 13 G) := hsubsingleton
    -- Step 6.23.2: Invoke the standard fact that a unique Sylow subgroup is normal.
    exact Sylow.normal_of_subsingleton (p := 13) (G := G) P
  -- Step 7: Assemble the required witness prime, Sylow subgroup, and properties.
  refine ⟨13, P, ?_⟩
  -- Step 7.1: Provide the primality of 13 and package the remaining goals.
  refine ⟨hprime13, ?_⟩
  -- Step 7.2: Present the divisibility and normality facts to finish the proof.
  exact ⟨hdiv_card, hnormal⟩
