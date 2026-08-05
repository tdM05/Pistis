import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that a group of order 200 has a normal Sylow 5-subgroup.
-/

/-Informal Proof

Let $G$ be a group of order $200=5^2 \cdot 8$. Note that 5 is a prime not dividing 8 . Let $P \in$ $S y l_5(G)$. [We know $P$ exists since $S y l_5(G) \neq \emptyset$ by Sylow's Theorem]

The number of Sylow 5-subgroups of $G$ is of the form $1+k \cdot 5$, i.e., $n_5 \equiv 1(\bmod 5)$ and $n_5$ divides 8 . The only such number that divides 8 and equals $1 (\bmod 5)$ is 1 so $n_5=1$. Hence $P$ is the unique Sylow 5-subgroup.
Since $P$ is the unique Sylow 5-subgroup, this implies that $P$ is normal in $G$.
-/

theorem Dummit_Foote_exercise_4_5_18 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 200) :
  ∃ N : Sylow 5 G, N.Normal := by
  -- Step 1: Work in classical logic to comfortably choose specific Sylow subgroups.
  classical
  -- Step 2: Record the primality of 5 and install it as a `Fact` for the Sylow API.
  have hprime5 : Nat.Prime 5 := by decide
  -- Step 2.1: Turn the primality proof into an instance needed by Sylow lemmas.
  haveI : Fact (Nat.Prime 5) := ⟨hprime5⟩
  -- Step 3: Choose a concrete Sylow 5-subgroup so we can talk about its index.
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 5 G))
  -- Step 4: Let n denote the number of Sylow 5-subgroups.
  set n : ℕ := Nat.card (Sylow 5 G) with hn
  -- Step 5: Record the Sylow congruence n ≡ 1 (mod 5).
  have hmod : n ≡ 1 [MOD 5] := by
    -- Step 5.1: Apply the standard congruence result and rewrite in terms of n.
    simpa [n] using (card_sylow_modEq_one (p := 5) (G := G))
  -- Step 6: Recall that 5 does not divide n, another outcome of Sylow's third theorem.
  have hnotdiv : ¬ 5 ∣ n := by
    -- Step 6.1: Express the non-divisibility using the dedicated lemma.
    simpa [n] using (not_dvd_card_sylow (p := 5) (G := G))
  -- Step 7: The number n divides the index of our chosen Sylow subgroup.
  have hdiv_index : n ∣ P.index := by
    -- Step 7.1: Invoke the divisibility between the Sylow count and the index.
    simpa [n] using (Sylow.card_dvd_index (p := 5) (G := G) P)
  -- Step 8: Understand the arithmetic size of the index by relating it to the whole group.
  have hindex_dvd_card : P.index ∣ card G := by
    -- Step 8.1: Translate the statement into the natural-number formulation of cardinals.
    simpa [Nat.card_eq_fintype_card] using (P.1.index_dvd_card)
  -- Step 8.2: Replace |G| with the concrete value 200.
  have hindex_dvd200 : P.index ∣ 200 := by
    -- Step 8.2.1: Substitute the given group order and keep the divisor relation.
    simpa [hG] using hindex_dvd_card
  -- Step 9: Show that 5 does not divide the index, using the Sylow normalizer fact.
  have hnot_dvd_index : ¬ 5 ∣ P.index := by
    -- Step 9.1: Invoke the standard lemma about indices of Sylow subgroups.
    simpa using (Sylow.not_dvd_index (p := 5) (G := G) P)
  -- Step 10: From the non-divisibility, deduce that the index is coprime to 25 = 5^2.
  have hcoprime_index_pow : Nat.Coprime P.index (5 ^ 2) :=
    -- Step 10.1: Use the prime-specific coprimality lemma with exponent two.
    hprime5.coprime_pow_of_not_dvd hnot_dvd_index
  -- Step 10.2: Rewrite the previous statement numerically as coprimality with 25.
  have hcoprime_index25 : Nat.Coprime P.index 25 := by
    -- Step 10.2.1: Observe that 5^2 equals 25.
    simpa using hcoprime_index_pow
  -- Step 11: View 200 as 25 * 8 to prepare for cancelling the factor 25.
  have h200 : 200 = 25 * 8 := by decide
  -- Step 11.1: Turn the divisor relation with 200 into one with 25 * 8 explicitly.
  have hindex_dvdMul : P.index ∣ 25 * 8 := by simpa [h200] using hindex_dvd200
  -- Step 12: Cancel the factor 25 thanks to coprimality and conclude P.index ∣ 8.
  have hindex_dvd8 : P.index ∣ 8 :=
    -- Step 12.1: Apply the coprime cancellation lemma on the left factor.
    hcoprime_index25.dvd_of_dvd_mul_left hindex_dvdMul
  -- Step 13: Combine the two divisor relations to see that n divides 8.
  have hndvd8 : n ∣ 8 := Nat.dvd_trans hdiv_index hindex_dvd8
  -- Step 14: Since the type of Sylow subgroups is nonempty, n is strictly positive.
  have hpos : 0 < n := by
    -- Step 14.1: POSitivity results from the mere existence of a Sylow subgroup.
    have : 0 < Nat.card (Sylow 5 G) := Nat.card_pos
    -- Step 14.2: Rewrite that inequality in terms of n.
    simpa [n] using this
  -- Step 15: Convert the positivity into a lower bound useful for modular arguments.
  have hle_one : 1 ≤ n := Nat.succ_le_of_lt hpos
  -- Step 16: From the congruence n ≡ 1 (mod 5), conclude that n - 1 is divisible by 5.
  have hdiv_minus : 5 ∣ n - 1 := (Nat.modEq_iff_dvd' hle_one).1 hmod.symm
  -- Step 16.1: Introduce an integer k with n = 5 * k + 1.
  obtain ⟨k, hk⟩ := hdiv_minus
  -- Step 16.2: Repackage the previous equality into a convenient explicit expression.
  have hkdef : n = 5 * k + 1 := by
    -- Step 16.2.1: Add 1 back to both sides of n - 1 = 5 * k.
    have hSubAdd : (n - 1) + 1 = n := Nat.sub_add_cancel hle_one
    simpa [hk, add_comm, add_left_comm, add_assoc] using hSubAdd.symm
  -- Step 17: Transfer the divisor relation n ∣ 8 into an upper bound using positivity.
  have hle8 : n ≤ 8 := Nat.le_of_dvd (by decide : 0 < 8) hndvd8
  -- Step 17.1: Rewrite the bound in terms of k using the explicit formula for n.
  have hk_bound : 5 * k ≤ 7 := by
    -- Step 17.1.1: Move the +1 past the inequality by taking successors.
    have hk_succ : Nat.succ (5 * k) ≤ Nat.succ 7 := by
      -- Step 17.1.1.1: Notice that successor corresponds precisely to adding 1.
      simpa [Nat.succ_eq_add_one, hkdef] using hle8
    -- Step 17.1.2: Drop successors on both sides to obtain the desired bound.
    exact (Nat.succ_le_succ_iff).1 hk_succ
  -- Step 18: Prove that k cannot be at least 2, hence k ≤ 1.
  have hk_le1 : k ≤ 1 := by
    -- Step 18.1: Argue by contradiction with the hypothesis k ≥ 2.
    by_contra hk_gt
    -- Step 18.2: Turn negated inequality into the concrete bound k ≥ 2.
    have hk_ge2 : 2 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_not_ge hk_gt)
    -- Step 18.3: Multiply the inequality by 5 to compare with hk_bound.
    have hk_ge10 : 10 ≤ 5 * k := by
      -- Step 18.3.1: Use monotonicity of multiplication by the positive number 5.
      have := Nat.mul_le_mul_left 5 hk_ge2
      -- Step 18.3.2: Simplify the inequality numerically.
      simpa using this
    -- Step 18.4: Contradict the previously obtained upper bound.
    have hk_contra : 10 ≤ 7 := le_trans hk_ge10 hk_bound
    -- Step 18.5: Close the contradiction with the obvious arithmetic fact.
    exact (by decide : ¬ 10 ≤ 7) hk_contra
  -- Step 19: Narrow k down to the two numerical possibilities 0 or 1.
  have hk_cases : k = 0 ∨ k = 1 := by
    -- Step 19.1: Inspect k directly using the inequality k ≤ 1.
    cases hk : k with
    | zero =>
        -- Step 19.1.1: If k = 0, we have the first case immediately.
        exact Or.inl rfl
    | succ k' =>
        -- Step 19.1.2: Analyze the case k = k' + 1 in light of hk_le1.
        have hk_succ_le : Nat.succ k' ≤ Nat.succ 0 := by
          -- Step 19.1.2.1: Rewrite using the inequality k ≤ 1.
          simpa [hk, Nat.succ_eq_add_one] using hk_le1
        -- Step 19.1.2.2: Deduce that k' must equal 0.
        have hk'_zero : k' = 0 := le_antisymm ((Nat.succ_le_succ_iff).1 hk_succ_le) (Nat.zero_le _)
        -- Step 19.1.2.3: Conclude that k = 1.
        exact Or.inr (by simp [hk'_zero])
  -- Step 20: Rule out the possibility k = 1 because it violates the divisibility n ∣ 8.
  have hk0 : k = 0 := by
    -- Step 20.1: Check the two cases individually.
    cases hk_cases with
    | inl hk_zero =>
        -- Step 20.1.1: The case k = 0 works perfectly.
        exact hk_zero
    | inr hk_one =>
        -- Step 20.1.2: If k = 1, then n = 6, giving an impossible divisor of 8.
        -- Step 20.1.2.1: Compute the explicit value of n when k = 1.
        have hk_n : n = 6 := by
          simp [hkdef, hk_one]
        -- Step 20.1.2.2: Rewrite the divisor relation using n = 6.
        -- Step 20.1.2.2: Reach a contradiction because 6 does not divide 8.
        simp [hk_n] at hndvd8
  -- Step 21: Substitute k = 0 back to obtain n = 1 explicitly.
  have hcardOne : n = 1 := by
    -- Step 21.1: Replace k with 0 in the expression n = 5 * k + 1.
    simp [hkdef, hk0]
  -- Step 22: Translate the equality on n into the expected statement about the Sylow type.
  have hcardNat : Nat.card (Sylow 5 G) = 1 := by simpa [n] using hcardOne
  -- Step 23: Deduce that the type of Sylow 5-subgroups is a subsingleton.
  have hsubsingleton : Subsingleton (Sylow 5 G) :=
    (Nat.card_eq_one_iff_unique).1 hcardNat |>.1
  -- Step 24: Convert the subsingleton information into normality of our chosen Sylow subgroup.
  have hnormal : P.Normal := by
    -- Step 24.1: Install the subsingleton structure as an instance.
    letI : Subsingleton (Sylow 5 G) := hsubsingleton
    -- Step 24.2: Invoke the uniqueness-to-normality lemma.
    exact Sylow.normal_of_subsingleton (p := 5) (G := G) P
  -- Step 25: Package the chosen Sylow subgroup together with the normality proof.
  exact ⟨P, hnormal⟩
