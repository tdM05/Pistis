import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that a group of order 351 has a normal Sylow $p$-subgroup for some prime $p$ dividing its order.
-/

/-Informal Proof

Since $|G|=351=3^{2}.13$, $G$ has $3-$Sylow subgroup of order $9$, as well as $13-$Sylow subgroup of order $13$. Now, we count the number of such subgroups. Let $n_{13}$ be the number of $13-$Sylow subgroup and $n_{3}$ be the number of  $3-$Sylow subgroup. Now $n_{13}=1+13k$ where $1+13k|9$. The choices for $k$ is $0$. Hence, there is a unique $13-$Sylow subgroup and hence is normal.
-/

theorem Dummit_Foote_exercise_4_5_15 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 351) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧  P.Normal := by
  /-
  **Proof Strategy:**
  We prove by contradiction using a counting argument.

  Key insight: 351 = 3² × 13

  For p = 13: n₁₃ ≡ 1 (mod 13) and n₁₃ | 27. So n₁₃ ∈ {1, 27}.
  For p = 3:  n₃ ≡ 1 (mod 3) and n₃ | 13. So n₃ ∈ {1, 13}.

  We cannot have BOTH n₁₃ = 27 AND n₃ = 13:
  - If n₁₃ = 27: there are 27 × 12 = 324 elements of order 13.
  - Remaining elements: 351 - 324 = 27 (including identity).
  - But if n₃ = 13, and each Sylow 3-subgroup has 9 elements:
    Even with maximum overlap, 13 Sylow 3-subgroups can't fit in 27 elements
    (they need at least 1 + 13 × 8 = 105 elements for the non-identity elements
     plus identity, assuming pairwise intersections are trivial).

  So at least one of n₁₃ = 1 or n₃ = 1, meaning at least one Sylow subgroup is normal.

  We will show that n₁₃ = 1 specifically by analyzing the constraints.
  -/
  -- Step 1: Enable classical logic for case analysis
  classical
  -- Step 2: Establish primality facts
  have hprime13 : Nat.Prime 13 := by decide
  have hprime3 : Nat.Prime 3 := by decide
  haveI : Fact (Nat.Prime 13) := ⟨hprime13⟩
  haveI : Fact (Nat.Prime 3) := ⟨hprime3⟩
  -- Step 3: Verify basic divisibility
  have hdiv13 : 13 ∣ card G := by simp only [hG]; decide
  have hdiv3 : 3 ∣ card G := by simp only [hG]; decide
  -- Step 4: Get Sylow subgroups
  obtain ⟨P13⟩ := (inferInstance : Nonempty (Sylow 13 G))
  obtain ⟨P3⟩ := (inferInstance : Nonempty (Sylow 3 G))
  -- Step 5: Set up the counting for Sylow 13-subgroups
  set n13 : ℕ := Nat.card (Sylow 13 G) with hn13
  -- Step 5.1: n₁₃ ≡ 1 (mod 13)
  have hmod13 : n13 ≡ 1 [MOD 13] := by
    simpa [n13] using (card_sylow_modEq_one (p := 13) (G := G))
  -- Step 5.2: 13 does not divide n₁₃
  have hnotdiv13 : ¬ 13 ∣ n13 := by
    simpa [n13] using (not_dvd_card_sylow (p := 13) (G := G))
  -- Step 5.3: n₁₃ divides the index of P13
  have hdiv_index13 : n13 ∣ P13.index := by
    simpa [n13] using (Sylow.card_dvd_index (p := 13) (G := G) P13)
  -- Step 5.4: P13.index divides |G|
  have hindex_dvd13 : P13.index ∣ card G := by
    simpa [Nat.card_eq_fintype_card] using (P13.1.index_dvd_card)
  -- Step 5.5: So n₁₃ divides |G| = 351
  have hdvd_cardG13 : n13 ∣ card G := Nat.dvd_trans hdiv_index13 hindex_dvd13
  have hdvd351_13 : n13 ∣ 351 := by simpa [hG] using hdvd_cardG13
  -- Step 5.6: n₁₃ is coprime to 13
  have hcoprime13 : Nat.Coprime n13 13 := by
    simpa [Nat.coprime_comm] using (hprime13.coprime_iff_not_dvd).2 hnotdiv13
  -- Step 5.7: Since 351 = 13 × 27, we have n₁₃ | 27
  have h351 : 351 = 13 * 27 := by decide
  have hdvd27 : n13 ∣ 27 := by
    have hdvdMul : n13 ∣ 13 * 27 := by simpa [h351] using hdvd351_13
    exact hcoprime13.dvd_of_dvd_mul_left hdvdMul
  -- Step 5.8: n₁₃ > 0 since Sylow 13-subgroups exist
  have hpos13 : 0 < n13 := by
    have : 0 < Nat.card (Sylow 13 G) := Nat.card_pos
    simpa [n13] using this
  -- Step 5.9: n₁₃ ≤ 27
  have hle27 : n13 ≤ 27 := Nat.le_of_dvd (by decide : 0 < 27) hdvd27
  -- Step 5.10: n₁₃ ≥ 1
  have h1le13 : 1 ≤ n13 := Nat.succ_le_of_lt hpos13
  -- Step 5.11: 13 | (n₁₃ - 1)
  have hdvdminus13 : 13 ∣ n13 - 1 := (Nat.modEq_iff_dvd' h1le13).1 hmod13.symm
  -- Step 5.12: Write n₁₃ = 13k + 1 for some k
  obtain ⟨k13, hk13eq⟩ := hdvdminus13
  have hn13def : n13 = 13 * k13 + 1 := by
    have hSubAdd : (n13 - 1) + 1 = n13 := Nat.sub_add_cancel h1le13
    calc
      n13 = (n13 - 1) + 1 := hSubAdd.symm
      _ = 13 * k13 + 1 := by simp [hk13eq, add_comm]
  -- Step 5.13: From n₁₃ ≤ 27 we get 13k + 1 ≤ 27
  have hk13Bound : 13 * k13 + 1 ≤ 27 := by simpa [hn13def] using hle27
  -- Step 5.14: So 13k ≤ 26, hence k ≤ 2
  have hk13_le26 : 13 * k13 ≤ 26 := by
    have hk_succ : Nat.succ (13 * k13) ≤ Nat.succ 26 := by
      simpa [Nat.succ_eq_add_one, hn13def] using hk13Bound
    exact (Nat.succ_le_succ_iff).1 hk_succ
  have hk13_le2 : k13 ≤ 2 := by
    by_contra hk_gt
    have hk_ge3 : 3 ≤ k13 := Nat.succ_le_of_lt (Nat.lt_of_not_ge hk_gt)
    have hk_ge39 : 39 ≤ 13 * k13 := by
      have := Nat.mul_le_mul_left 13 hk_ge3
      simpa using this
    have hk_contra : 39 ≤ 26 := le_trans hk_ge39 hk13_le26
    exact (by decide : ¬ 39 ≤ 26) hk_contra
  -- Step 5.15: So k ∈ {0, 1, 2}, meaning n₁₃ ∈ {1, 14, 27}
  -- But n₁₃ | 27, and 14 ∤ 27, so n₁₃ ∈ {1, 27}
  have hk13_cases : k13 = 0 ∨ k13 = 1 ∨ k13 = 2 := by
    omega
  -- Step 6: Now set up counting for Sylow 3-subgroups
  set n3 : ℕ := Nat.card (Sylow 3 G) with hn3
  -- Step 6.1: n₃ ≡ 1 (mod 3)
  have hmod3 : n3 ≡ 1 [MOD 3] := by
    simpa [n3] using (card_sylow_modEq_one (p := 3) (G := G))
  -- Step 6.2: 3 does not divide n₃
  have hnotdiv3 : ¬ 3 ∣ n3 := by
    simpa [n3] using (not_dvd_card_sylow (p := 3) (G := G))
  -- Step 6.3: n₃ divides the index of P3
  have hdiv_index3 : n3 ∣ P3.index := by
    simpa [n3] using (Sylow.card_dvd_index (p := 3) (G := G) P3)
  -- Step 6.4: P3.index divides |G|
  have hindex_dvd3 : P3.index ∣ card G := by
    simpa [Nat.card_eq_fintype_card] using (P3.1.index_dvd_card)
  -- Step 6.5: So n₃ divides |G| = 351
  have hdvd_cardG3 : n3 ∣ card G := Nat.dvd_trans hdiv_index3 hindex_dvd3
  have hdvd351_3 : n3 ∣ 351 := by simpa [hG] using hdvd_cardG3
  -- Step 6.6: n₃ is coprime to 3
  have hcoprime3 : Nat.Coprime n3 3 := by
    simpa [Nat.coprime_comm] using (hprime3.coprime_iff_not_dvd).2 hnotdiv3
  -- Step 6.7: Since 351 = 3² × 39 = 9 × 39, and 351 = 3 × 117, we have n₃ | 13
  -- Actually 351 = 9 × 39 = 9 × 39, but 39 = 3 × 13, so 351 = 27 × 13 = 3³ × 13?
  -- Let me check: 3² = 9, 9 × 39 = 351, but 39 = 3 × 13, so 351 = 3³ × 13
  -- Wait, 3³ = 27, 27 × 13 = 351. Yes!
  -- So 351 = 3³ × 13, meaning the Sylow 3-subgroup has order 27, not 9!
  -- Let me recalculate...
  -- Actually: 351 / 3 = 117, 117 / 3 = 39, 39 / 3 = 13. So 351 = 3³ × 13.
  -- But the problem says 351 = 3² × 13... let me verify.
  -- 3² × 13 = 9 × 13 = 117 ≠ 351.
  -- 3³ × 13 = 27 × 13 = 351. ✓
  -- So the informal proof has an error! 351 = 27 × 13 = 3³ × 13, not 3² × 13.
  -- So Sylow 3-subgroups have order 27, and there are n₃ of them where n₃ | 13 and n₃ ≡ 1 (mod 3).
  -- Divisors of 13: {1, 13}, both ≡ 1 (mod 3). So n₃ ∈ {1, 13}.
  have h351_alt : 351 = 27 * 13 := by decide
  have h351_27 : 351 = 3 * 117 := by decide
  have hcoprime3_factor : Nat.Coprime 3 13 := by decide
  -- Since n₃ | 351 and gcd(n₃, 3) = 1, we need to find what n₃ divides
  -- 351 = 3³ × 13, and n₃ is coprime to 3, so n₃ | 13
  have hdvd13_n3 : n3 ∣ 13 := by
    -- n₃ | 351 = 27 × 13, and gcd(n₃, 27) = 1 (since gcd(n₃, 3) = 1)
    have hcoprime27 : Nat.Coprime n3 27 := by
      have h27 : 27 = 3^3 := by decide
      rw [h27]
      exact Nat.Coprime.pow_right 3 hcoprime3
    have hdvdMul : n3 ∣ 27 * 13 := by simpa [h351_alt] using hdvd351_3
    exact hcoprime27.dvd_of_dvd_mul_left hdvdMul
  -- Step 6.8: n₃ > 0
  have hpos3 : 0 < n3 := by
    have : 0 < Nat.card (Sylow 3 G) := Nat.card_pos
    simpa [n3] using this
  -- Step 6.9: So n₃ ∈ {1, 13}
  have hn3_cases : n3 = 1 ∨ n3 = 13 := by
    have hle13 : n3 ≤ 13 := Nat.le_of_dvd (by decide : 0 < 13) hdvd13_n3
    have hge1 : 1 ≤ n3 := Nat.succ_le_of_lt hpos3
    -- n₃ | 13 and 13 is prime, so n₃ ∈ {1, 13}
    have hdiv_prime : n3 = 1 ∨ n3 = 13 := by
      have : n3 ∣ 13 := hdvd13_n3
      have h13prime := hprime13
      rcases (Nat.dvd_prime h13prime).mp this with h1 | h13
      · exact Or.inl h1
      · exact Or.inr h13
    exact hdiv_prime
  -- Step 7: Now we use the constraint that k₁₃ ≠ 1 (since 14 ∤ 27)
  have hn13_not14 : n13 ≠ 14 := by
    intro h
    simp [h] at hdvd27
  -- Step 8: So n₁₃ = 1 or n₁₃ = 27
  have hn13_cases_refined : n13 = 1 ∨ n13 = 27 := by
    cases hk13_cases with
    | inl h0 =>
      left
      simp [hn13def, h0]
    | inr h12 =>
      cases h12 with
      | inl h1 =>
        -- k = 1 means n₁₃ = 14, but we showed n₁₃ ≠ 14
        exfalso
        have : n13 = 14 := by simp [hn13def, h1]
        exact hn13_not14 this
      | inr h2 =>
        right
        simp [hn13def, h2]
  -- Step 9: If n₁₃ = 1, the Sylow 13-subgroup is unique and hence normal. Done!
  -- If n₁₃ = 27, we show n₃ = 1 by a counting argument.
  cases hn13_cases_refined with
  | inl hn13_eq1 =>
    -- Case: n₁₃ = 1, so the Sylow 13-subgroup is unique (hence normal)
    -- Step 9.1: Translate to Nat.card
    have hcardNat13 : Nat.card (Sylow 13 G) = 1 := by simpa [n13] using hn13_eq1
    -- Step 9.2: Sylow 13 G is a subsingleton
    have hsubsingleton13 : Subsingleton (Sylow 13 G) :=
      (Nat.card_eq_one_iff_unique).1 hcardNat13 |>.1
    -- Step 9.3: P13 is normal
    have hnormal13 : P13.Normal := by
      letI : Subsingleton (Sylow 13 G) := hsubsingleton13
      exact Sylow.normal_of_subsingleton (p := 13) (G := G) P13
    -- Step 9.4: Assemble the witness
    exact ⟨13, P13, hprime13, hdiv13, hnormal13⟩
  | inr hn13_eq27 =>
    -- Case: n₁₃ = 27, we need to show n₃ = 1
    -- Step 9.1: Counting argument - if n₁₃ = 27, there are 27 × 12 = 324 elements of order 13
    -- Step 9.2: Remaining elements: 351 - 324 = 27
    -- Step 9.3: If n₃ = 13, there would be too many elements
    -- But this is hard to formalize directly. Instead, we use a different approach:
    -- The Sylow 3-subgroups must fit within the 27 remaining elements.
    -- A Sylow 3-subgroup has order 27 (since 351 = 3³ × 13).
    -- If there are 13 Sylow 3-subgroups each of order 27, they must all be the same subgroup!
    -- Wait, that's not right either. Let me think...
    -- Actually, the Sylow 3-subgroup has order 27 = 3³.
    -- If n₃ = 13, the 13 Sylow 3-subgroups together with the Sylow 13-subgroups
    -- must account for all 351 elements.
    -- Elements in Sylow 13-subgroups: 27 × 12 = 324 (non-identity of order 13) + 1 (identity) = 325? No wait.
    -- Actually, the identity is in every subgroup. Let me be more careful.
    -- Elements of order 13: exactly 27 × 12 = 324 (each Sylow 13-subgroup has 12 non-identity elements)
    -- Elements NOT of order 13 (including identity): 351 - 324 = 27
    -- These 27 elements form a single Sylow 3-subgroup!
    -- Wait, yes! If n₁₃ = 27, the 27 non-order-13 elements must contain all Sylow 3-subgroups.
    -- But a Sylow 3-subgroup has order 27, so there's exactly one, hence n₃ = 1!
    -- This is the key insight.
    -- Step 9.4: We need n₃ = 1
    have hn3_eq1 : n3 = 1 := by
      -- We prove this by showing n₃ ≠ 13
      cases hn3_cases with
      | inl h => exact h
      | inr h13 =>
        -- Assume n₃ = 13, derive contradiction
        -- If n₁₃ = 27 and n₃ = 13, we get a counting contradiction
        -- The elements of order 13: Each Sylow 13-subgroup is cyclic of order 13,
        -- contributing 12 elements of order 13. Two distinct Sylow 13-subgroups
        -- intersect only at identity (since |P ∩ Q| divides 13 and < 13).
        -- So total elements of order 13: 27 × 12 = 324.
        --
        -- Remaining elements: 351 - 324 = 27.
        -- A Sylow 3-subgroup has order 27 (since the 3-part of 351 is 27).
        -- So any Sylow 3-subgroup is a subset of these 27 elements.
        -- But if P is a Sylow 3-subgroup with |P| = 27 and P ⊆ {27 elements},
        -- then P = {27 elements}. So there's exactly one Sylow 3-subgroup, n₃ = 1.
        --
        -- This contradicts n₃ = 13.
        exfalso
        -- We'll formalize this using cardinality bounds
        -- First, establish that Sylow 3-subgroups have order 27
        have hcard_P3 : card P3 = 27 := by
          have h := Sylow.card_eq_multiplicity (p := 3) P3
          simp only [Nat.card_eq_fintype_card, hG] at h
          -- 351 = 3³ × 13, so factorization 3 of 351 = 3
          have hfact : (351 : ℕ).factorization 3 = 3 := by native_decide
          simp only [hfact, pow_succ, pow_zero, one_mul] at h
          omega
        -- Similarly, Sylow 13-subgroups have order 13
        have hcard_P13 : card P13 = 13 := by
          have h := Sylow.card_eq_multiplicity (p := 13) P13
          simp only [Nat.card_eq_fintype_card, hG] at h
          have hfact : (351 : ℕ).factorization 13 = 1 := by native_decide
          simp only [hfact, pow_one] at h
          exact h
        -- Now, if n₁₃ = 27, each Sylow 13-subgroup contributes 12 distinct elements of order 13
        -- (these subgroups are cyclic of prime order, so pairwise intersection is trivial)
        -- Total distinct elements in all Sylow 13-subgroups (not counting overcounting):
        -- Actually we need to count more carefully.
        -- Each Sylow 13-subgroup has 13 elements.
        -- Two distinct Sylow 13-subgroups P, Q: |P ∩ Q| divides |P| = 13 (prime), so |P ∩ Q| = 1.
        -- So distinct Sylow 13-subgroups intersect only at identity.
        -- Total elements in ⋃ of all Sylow 13-subgroups: 1 + 27 × 12 = 325.
        -- Wait, that's more than 351! Let me reconsider.
        -- No wait, 1 + 27 × 12 = 1 + 324 = 325 ≤ 351. OK, not a contradiction yet.
        --
        -- Elements NOT in any Sylow 13-subgroup: 351 - 325 = 26.
        -- But we also need to fit Sylow 3-subgroups. A Sylow 3-subgroup has 27 elements.
        -- Can a Sylow 3-subgroup contain elements of order 13? No, because:
        --   - Elements of a 3-group have order a power of 3.
        --   - Order 13 is not a power of 3.
        -- So Sylow 3-subgroups consist only of elements whose order is a power of 3.
        -- These elements are NOT of order 13.
        --
        -- Let T = elements not of order 13 (including identity).
        -- |T| = 351 - 324 = 27 (counting identity and non-order-13 non-identity elements).
        -- Wait, 324 is the count of elements of order EXACTLY 13 (non-identity).
        -- So |T| = 351 - 324 = 27.
        -- Every Sylow 3-subgroup P3 has |P3| = 27 and P3 ⊆ T (since P3 elements have order 3^k, not 13).
        -- But |P3| = |T| = 27, so P3 = T.
        -- This means there's exactly one Sylow 3-subgroup, contradicting n₃ = 13.

        -- To formalize: we need to show that the union of all Sylow 13-subgroups
        -- has at most 1 + 27 × 12 = 325 elements, leaving at least 26 elements outside.
        -- But wait, I computed |T| = 27, and |P3| = 27, so P3 ⊆ T implies P3 = T (as sets).
        -- Hence there's only one Sylow 3-subgroup.

        -- This is getting complex. Let me try a simpler approach using the fact that
        -- the index formula gives us what we need.
        --
        -- Alternative: Use Sylow.card_eq_index_normalizer
        -- Nat.card (Sylow 3 G) = P3.normalizer.index
        -- So 13 = P3.normalizer.index
        -- And P3.normalizer.index = |G| / |N_G(P3)| = 351 / |N_G(P3)|
        -- So |N_G(P3)| = 351 / 13 = 27.
        -- But P3 ≤ N_G(P3) (every subgroup is contained in its normalizer).
        -- And |P3| = 27, |N_G(P3)| = 27, so P3 = N_G(P3).
        -- This means P3 is its own normalizer.
        --
        -- Now, in a group of order 351 = 3³ × 13, if a Sylow 3-subgroup P3 has N_G(P3) = P3,
        -- then by the N/C theorem (or Burnside's transfer theorem), there might be constraints.
        -- But this is also complex.
        --
        -- Let me try yet another approach: direct omega/decide
        -- We have: 27 × 12 = 324 elements of order 13
        -- Remaining: 351 - 324 = 27 elements
        -- If n₃ = 13, we need 13 Sylow 3-subgroups of order 27 to fit in... wait, they can overlap.
        -- But the identity is in all of them. Let's count more carefully.
        --
        -- Actually, let me use a key fact: in a p-group, the only element of order 1 is identity.
        -- So distinct Sylow 3-subgroups can share identity and other elements.
        --
        -- Hmm, this counting argument is getting complicated.
        -- Let me try a different approach: use the fact that n₃ × (|P3| - |N_G(P3) ∩ P3|) ≤ something.
        --
        -- Actually, I think the cleanest approach is to use the orbit-stabilizer theorem
        -- or the fact that |Sylow p G| = [G : N_G(P)] for any Sylow p-subgroup P.
        --
        -- For Sylow 3-subgroups: n₃ = [G : N_G(P3)] = 351 / |N_G(P3)|
        -- If n₃ = 13, then |N_G(P3)| = 27 = |P3|, so N_G(P3) = P3.
        --
        -- For Sylow 13-subgroups: n₁₃ = [G : N_G(P13)] = 351 / |N_G(P13)|
        -- If n₁₃ = 27, then |N_G(P13)| = 13 = |P13|, so N_G(P13) = P13.
        --
        -- Now, if both N_G(P3) = P3 and N_G(P13) = P13, we have:
        -- |N_G(P3)| = 27, |N_G(P13)| = 13.
        --
        -- Consider the subgroup H = P3 P13 (product of subgroups).
        -- |H| = |P3| × |P13| / |P3 ∩ P13| = 27 × 13 / |P3 ∩ P13|.
        -- Since |P3 ∩ P13| divides gcd(27, 13) = 1, we have |P3 ∩ P13| = 1.
        -- So |H| = 27 × 13 = 351 = |G|, hence H = G.
        --
        -- This means G = P3 P13 = P3 × P13 (as sets, since intersection is trivial).
        -- Actually, P3 and P13 are both subgroups, and P3 ∩ P13 = {1}, so the product
        -- P3 P13 has |P3 P13| = 351 = |G|, so P3 P13 = G.
        --
        -- Now, P3 is normal in P3 P13 = G? Not necessarily, unless P13 normalizes P3.
        -- But P13 ∩ N_G(P3) = P13 ∩ P3 = {1} (since N_G(P3) = P3 and P3 ∩ P13 = {1}).
        -- Wait, that's not right. N_G(P3) = P3 means P3 ≤ N_G(P3) and |N_G(P3)| = |P3|,
        -- so N_G(P3) = P3. But P13 might normalize P3 if conjugation by P13 fixes P3.
        --
        -- Actually, if N_G(P3) = P3, then the only elements that normalize P3 are in P3.
        -- So P13 ∩ N_G(P3) = P13 ∩ P3 = {1}.
        -- This means no non-identity element of P13 normalizes P3.
        -- But wait, G = P3 P13, so for any g ∈ G, g = p3 × p13 for some p3 ∈ P3, p13 ∈ P13.
        -- If g ∈ N_G(P3), then g = p3 p13 normalizes P3.
        -- Since p3 ∈ P3 ≤ N_G(P3), we have p13 ∈ N_G(P3) (because N_G(P3) is a subgroup).
        -- But p13 ∈ P13 ∩ N_G(P3) = {1}, so p13 = 1, hence g = p3 ∈ P3.
        -- So N_G(P3) ⊆ P3, and P3 ⊆ N_G(P3), so N_G(P3) = P3. ✓ (consistent)
        --
        -- Now, consider the action of P13 on the set of Sylow 3-subgroups by conjugation.
        -- There are 13 Sylow 3-subgroups, and P13 acts on them.
        -- The orbit of P3 under P13 has size |P13| / |Stab_{P13}(P3)| = 13 / |P13 ∩ N_G(P3)| = 13 / 1 = 13.
        -- So the P13-orbit of P3 has all 13 Sylow 3-subgroups!
        --
        -- This means P13 acts transitively on the Sylow 3-subgroups.
        --
        -- Now, consider the total number of elements in the union of all Sylow 3-subgroups.
        -- If all 13 Sylow 3-subgroups are distinct, and they pairwise intersect in subgroups:
        -- For two distinct Sylow 3-subgroups Q, R, |Q ∩ R| divides |Q| = 27 = 3³.
        -- The intersection Q ∩ R is a 3-group, so |Q ∩ R| ∈ {1, 3, 9, 27}.
        -- If |Q ∩ R| = 27, then Q = R, contradiction.
        --
        -- By Inclusion-Exclusion, the union has at least:
        -- 13 × 27 - C(13,2) × 9 = 351 - 78 × 9 = 351 - 702 < 0, which is absurd.
        -- OK that bound is too loose.
        --
        -- Let me try a different approach. Since we're in Lean, let me just use
        -- the fact that the argument is getting complicated and instead use decide/omega
        -- on the specific numerical constraints.
        --
        -- Actually, I realize there's a much simpler approach!
        --
        -- KEY INSIGHT: Elements of order 13 cannot be in any Sylow 3-subgroup.
        -- If n₁₃ = 27, there are 27 Sylow 13-subgroups.
        -- Total elements of order 13: the union of (P - {1}) over all Sylow 13-subgroups P.
        -- Since Sylow 13-subgroups have prime order, distinct ones intersect only at {1}.
        -- So |⋃ (P - {1})| = 27 × 12 = 324.
        --
        -- Elements NOT of order 13: 351 - 324 = 27.
        -- This includes identity and all elements whose order divides 27 (i.e., 1, 3, 9, 27).
        --
        -- A Sylow 3-subgroup Q has |Q| = 27 and all elements have order dividing 27.
        -- So Q ⊆ {elements not of order 13}.
        -- But |Q| = 27 = |{elements not of order 13}|.
        -- So Q = {elements not of order 13} (as sets).
        --
        -- This means there's EXACTLY ONE Sylow 3-subgroup!
        -- This contradicts n₃ = 13.
        --
        -- Now let me formalize this in Lean...
        -- This requires some machinery about unions and cardinalities.
        -- Let me check if there's a simpler Mathlib lemma.

        /-
        **COUNTING ARGUMENT PROOF:**

        We derive a contradiction from h13 : n₃ = 13 and hn13_eq27 : n₁₃ = 27.

        Key facts:
        1. |G| = 351 = 27 × 13 = 3³ × 13
        2. n₁₃ = 27 Sylow 13-subgroups, each of order 13 (prime)
        3. n₃ = 13 Sylow 3-subgroups, each of order 27

        Counting elements of order 13:
        - Each Sylow 13-subgroup Q has |Q| = 13 (prime order)
        - Non-identity elements of Q have order exactly 13
        - Distinct Sylow 13-subgroups intersect only at {1} (prime order)
        - Total elements of order 13: 27 × 12 = 324

        Counting elements not of order 13:
        - |G| - 324 = 351 - 324 = 27 elements

        Sylow 3-subgroups:
        - Each P has |P| = 27
        - All elements of P have order dividing 27 (a power of 3)
        - No element of P has order 13 (since 13 ∤ 27)
        - So P ⊆ {elements not of order 13}
        - But |P| = 27 = |{elements not of order 13}|
        - So P = {elements not of order 13}

        Conclusion:
        - All Sylow 3-subgroups equal {elements not of order 13}
        - Hence there's exactly one Sylow 3-subgroup: n₃ = 1
        - This contradicts h13 : n₃ = 13
        -/

        -- We formalize this by showing that two Sylow 3-subgroups must be equal,
        -- contradicting the assumption that n₃ = 13 > 1.

        -- Since there are at least 2 Sylow 3-subgroups (n₃ = 13), pick any two.
        -- Both have 27 elements with order not equal to 13.
        -- There are exactly 27 such elements in G.
        -- So both subgroups equal {x ∈ G | orderOf x ≠ 13}, hence they're equal.
        -- This contradicts n₃ > 1.

        -- The formal proof requires showing:
        -- (A) |{x ∈ G | orderOf x = 13}| = 324
        -- (B) |{x ∈ G | orderOf x ≠ 13}| = 27
        -- (C) Any Sylow 3-subgroup P satisfies P ⊆ {x | orderOf x ≠ 13}
        -- (D) |P| = 27 = |{x | orderOf x ≠ 13}|, so P = {x | orderOf x ≠ 13}
        -- (E) All Sylow 3-subgroups are equal, so n₃ = 1

        -- Step (C) is straightforward: elements of a 3-group have order 3^k,
        -- and 13 ≠ 3^k for any k.

        -- Step (A) requires showing distinct Sylow 13-subgroups are disjoint.

        -- For a complete formal proof, we establish these facts:

        -- Establish that Sylow 3-subgroup elements don't have order 13
        have hP3_order_not_13 : ∀ x ∈ (P3 : Subgroup G), orderOf x ≠ 13 := by
          intro x hx hord
          -- orderOf x divides |P3| = 27
          have h1 : orderOf (⟨x, hx⟩ : P3.toSubgroup) ∣ Fintype.card P3.toSubgroup := orderOf_dvd_card
          have h2 : orderOf (⟨x, hx⟩ : P3.toSubgroup) = orderOf x := (Subgroup.orderOf_coe _).symm
          rw [h2, hcard_P3] at h1
          -- But 13 ∤ 27
          have : 13 ∣ 27 := by rw [hord] at h1; exact h1
          exact (by decide : ¬ 13 ∣ 27) this

        -- Similarly for any Sylow 3-subgroup Q
        have hSylow3_order_not_13 : ∀ (Q : Sylow 3 G), ∀ x ∈ (Q : Subgroup G), orderOf x ≠ 13 := by
          intro Q x hx hord
          have hQ_card : Fintype.card Q = 27 := by
            have h := Sylow.card_eq_multiplicity (p := 3) Q
            simp only [Nat.card_eq_fintype_card, hG] at h
            have hfact : (351 : ℕ).factorization 3 = 3 := by native_decide
            simp only [hfact, pow_succ, pow_zero, one_mul] at h
            omega
          have h1 : orderOf (⟨x, hx⟩ : Q.toSubgroup) ∣ Fintype.card Q.toSubgroup := orderOf_dvd_card
          have h2 : orderOf (⟨x, hx⟩ : Q.toSubgroup) = orderOf x := (Subgroup.orderOf_coe _).symm
          rw [h2, hQ_card] at h1
          have : 13 ∣ 27 := by rw [hord] at h1; exact h1
          exact (by decide : ¬ 13 ∣ 27) this

        -- The set of non-order-13 elements contains all Sylow 3-subgroups
        -- Each Sylow 3-subgroup has 27 elements
        -- If there are 13 > 1 Sylow 3-subgroups, pick any two distinct ones
        -- Both must be contained in the set of non-order-13 elements
        -- But |non-order-13 elements| = 27 = |Sylow 3-subgroup|
        -- So each Sylow 3-subgroup equals the entire set of non-order-13 elements
        -- Hence all Sylow 3-subgroups are equal, contradicting n₃ > 1

        -- To complete this formally, we would need to:
        -- 1. Define the set S = {x ∈ G | orderOf x ≠ 13}
        -- 2. Show |S| = 27 using the disjointness of Sylow 13-subgroups
        -- 3. Show each Sylow 3-subgroup Q satisfies (Q : Set G) ⊆ S
        -- 4. Since |Q| = |S| = 27, conclude (Q : Set G) = S
        -- 5. Hence all Sylow 3-subgroups are equal as sets, so n₃ = 1

        -- The disjointness of Sylow 13-subgroups (for step 2):
        have hSylow13_disjoint : ∀ (Q R : Sylow 13 G), Q ≠ R →
            (Q : Subgroup G) ⊓ R = ⊥ := by
          intro Q R hQR
          rw [eq_bot_iff]
          intro x hx
          simp only [Subgroup.mem_inf, Subgroup.mem_bot] at hx ⊢
          by_contra hne
          -- x ∈ Q and x ∈ R, both Sylow 13-subgroups of prime order
          -- ⟨x⟩ ≤ Q ∩ R, and |⟨x⟩| = orderOf x which divides 13
          -- Since x ≠ 1, orderOf x = 13, so |⟨x⟩| = 13 = |Q| = |R|
          -- Hence ⟨x⟩ = Q = R, contradicting Q ≠ R
          have hQ_card_fintype : Fintype.card Q = 13 := by
            have h := Sylow.card_eq_multiplicity (p := 13) Q
            simp only [Nat.card_eq_fintype_card, hG] at h
            have hfact : (351 : ℕ).factorization 13 = 1 := by native_decide
            simp only [hfact, pow_one] at h
            exact h
          have hQ_card : Nat.card (Q : Subgroup G) = 13 := by
            simp only [Nat.card_eq_fintype_card, hQ_card_fintype]
          have horder_dvd : orderOf x ∣ 13 := by
            have h1 : orderOf (⟨x, hx.1⟩ : Q.toSubgroup) ∣ Fintype.card Q.toSubgroup := orderOf_dvd_card
            have h2 : orderOf (⟨x, hx.1⟩ : Q.toSubgroup) = orderOf x := (Subgroup.orderOf_coe _).symm
            rw [h2, hQ_card_fintype] at h1
            exact h1
          have horder_eq : orderOf x = 13 := by
            cases (Nat.dvd_prime (by decide : Nat.Prime 13)).mp horder_dvd with
            | inl h1 => exact absurd (orderOf_eq_one_iff.mp h1) hne
            | inr h => exact h
          have hzpow_card : Nat.card (Subgroup.zpowers x) = 13 := by
            rw [Nat.card_zpowers, horder_eq]
          have hzpow_le_Q : Subgroup.zpowers x ≤ Q := by
            intro y hy
            obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
            exact (Q : Subgroup G).zpow_mem hx.1 n
          have hzpow_le_R : Subgroup.zpowers x ≤ R := by
            intro y hy
            obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
            exact (R : Subgroup G).zpow_mem hx.2 n
          have hR_card : Nat.card (R : Subgroup G) = 13 := by
            have h := Sylow.card_eq_multiplicity (p := 13) R
            simp only [Nat.card_eq_fintype_card, hG] at h
            have hfact : (351 : ℕ).factorization 13 = 1 := by native_decide
            simp only [hfact, pow_one] at h
            simp only [Nat.card_eq_fintype_card, h]
          -- Use cardinality-based equality: zpowers x ≤ Q and both have 13 elements
          have hzpow_eq_Q : Subgroup.zpowers x = Q := by
            apply le_antisymm hzpow_le_Q
            intro y hy
            by_contra h_not
            have h_strict : Subgroup.zpowers x < Q.toSubgroup := lt_of_le_of_ne hzpow_le_Q (fun h => h_not (h ▸ hy))
            have h_card_lt : Nat.card (Subgroup.zpowers x) < Nat.card Q.toSubgroup := by
              have h_ssubset : (Subgroup.zpowers x : Set G) ⊂ (Q.toSubgroup : Set G) := h_strict
              have h_finite : (Q.toSubgroup : Set G).Finite := Set.toFinite _
              exact h_finite.card_lt_card h_ssubset
            rw [hzpow_card, hQ_card] at h_card_lt
            exact Nat.lt_irrefl 13 h_card_lt
          have hzpow_eq_R : Subgroup.zpowers x = R := by
            apply le_antisymm hzpow_le_R
            intro y hy
            by_contra h_not
            have h_strict : Subgroup.zpowers x < R.toSubgroup := lt_of_le_of_ne hzpow_le_R (fun h => h_not (h ▸ hy))
            have h_card_lt : Nat.card (Subgroup.zpowers x) < Nat.card R.toSubgroup := by
              have h_ssubset : (Subgroup.zpowers x : Set G) ⊂ (R.toSubgroup : Set G) := h_strict
              have h_finite : (R.toSubgroup : Set G).Finite := Set.toFinite _
              exact h_finite.card_lt_card h_ssubset
            rw [hzpow_card, hR_card] at h_card_lt
            exact Nat.lt_irrefl 13 h_card_lt
          have hQR_eq : Q = R := by
            apply Sylow.ext
            rw [← hzpow_eq_Q, hzpow_eq_R]
          exact hQR hQR_eq

        -- Given the above, |{x | orderOf x = 13}| = 27 × 12 = 324
        -- Hence |{x | orderOf x ≠ 13}| = 351 - 324 = 27

        -- Each Sylow 3-subgroup has 27 elements and is contained in {orderOf ≠ 13}
        -- So each equals {orderOf ≠ 13}, hence all are equal, so n₃ = 1.

        -- This contradicts h13 : n₃ = 13.
        -- We have established the mathematical argument above.

        -- For the formal Lean proof, we note that completing steps 1-5 requires
        -- significant Finset/Fintype machinery to count elements precisely.
        -- The mathematical argument is complete and sound.

        -- We complete this case with the established facts:
        -- h13 : n₃ = 13, but the counting shows n₃ = 1. Contradiction.

        -- Using the disjointness and counting, we derive False:
        -- The key fact is that all Sylow 3-subgroups must be equal,
        -- which contradicts h13 : n₃ = 13 > 1.

        -- We show all Sylow 3-subgroups are equal by showing they're all contained
        -- in the same set of 27 elements (those not of order 13) and each has 27 elements.
        --
        -- Define the set S = {x ∈ G | orderOf x = 13} (elements of order 13)
        -- We will count |S| = 324 using the disjointness of Sylow 13-subgroups.

        -- Step 1: Define the sets we need
        let S13 : Finset G := Finset.univ.filter (fun x => orderOf x = 13)
        let nonS13 : Finset G := Finset.univ.filter (fun x => orderOf x ≠ 13)

        -- Step 2: S13 and nonS13 partition G
        have hpartition : S13.card + nonS13.card = card G := by
          have hdisj : Disjoint S13 nonS13 := by
            rw [Finset.disjoint_filter]
            intro x _ h1 h2
            exact h2 h1
          have hunion : S13 ∪ nonS13 = Finset.univ := by
            ext x
            simp only [S13, nonS13, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro _; trivial
            · intro _
              by_cases h : orderOf x = 13
              · left; exact h
              · right; exact h
          have hcard := Finset.card_union_of_disjoint hdisj
          rw [hunion, Finset.card_univ] at hcard
          omega

        -- Step 3: Each non-identity element of a Sylow 13-subgroup has order 13
        have hSylow13_order : ∀ (Q : Sylow 13 G), ∀ x ∈ (Q : Subgroup G), x ≠ 1 → orderOf x = 13 := by
          intro Q x hx hne
          have hQ_card_fintype : Fintype.card Q = 13 := by
            have h := Sylow.card_eq_multiplicity (p := 13) Q
            simp only [Nat.card_eq_fintype_card, hG] at h
            have hfact : (351 : ℕ).factorization 13 = 1 := by native_decide
            simp only [hfact, pow_one] at h
            exact h
          have horder_dvd : orderOf x ∣ 13 := by
            have h1 : orderOf (⟨x, hx⟩ : Q.toSubgroup) ∣ Fintype.card Q.toSubgroup := orderOf_dvd_card
            have h2 : orderOf (⟨x, hx⟩ : Q.toSubgroup) = orderOf x := (Subgroup.orderOf_coe _).symm
            rw [h2, hQ_card_fintype] at h1
            exact h1
          cases (Nat.dvd_prime (by decide : Nat.Prime 13)).mp horder_dvd with
          | inl h1 => exact absurd (orderOf_eq_one_iff.mp h1) hne
          | inr h => exact h

        -- Step 4: Elements of order 13 are exactly the non-identity elements
        --         of the 27 Sylow 13-subgroups, and these are pairwise disjoint.
        --
        -- Count: Each Sylow 13-subgroup contributes 12 elements of order 13.
        -- By disjointness (hSylow13_disjoint), total is 27 × 12 = 324.

        -- Step 5: |S13| = 324
        -- This requires showing the elements of order 13 are exactly the union
        -- of (Q \ {1}) for all Sylow 13-subgroups Q.
        --
        -- Key fact: Every element of order 13 is contained in some Sylow 13-subgroup
        -- (since ⟨x⟩ is a 13-group and is contained in some Sylow 13-subgroup).
        have horder13_in_sylow : ∀ x : G, orderOf x = 13 → ∃ Q : Sylow 13 G, x ∈ (Q : Subgroup G) := by
          intro x hord
          have hzpow_pgroup : IsPGroup 13 (Subgroup.zpowers x) := by
            rw [IsPGroup.iff_card]
            use 1
            rw [Nat.card_zpowers, hord]
            simp only [pow_one]
          obtain ⟨Q, hQ⟩ := hzpow_pgroup.exists_le_sylow
          exact ⟨Q, hQ (Subgroup.mem_zpowers x)⟩

        -- Step 6: Count |S13| = 324 using disjoint union
        -- We define the families and count using inclusion-exclusion
        have hS13_card : S13.card = 324 := by
          -- Define families as Finset G for each Sylow 13-subgroup (non-identity elements)
          let families : Sylow 13 G → Finset G :=
            fun Q => (Q : Set G).toFinset.filter (· ≠ 1)

          -- Each family has 12 elements (|Q| - 1 = 13 - 1 = 12)
          have hfam_card : ∀ Q : Sylow 13 G, (families Q).card = 12 := by
            intro Q
            have hQ_card : Fintype.card Q = 13 := by
              have h := Sylow.card_eq_multiplicity (p := 13) Q
              simp only [Nat.card_eq_fintype_card, hG] at h
              have hfact : (351 : ℕ).factorization 13 = 1 := by native_decide
              simp only [hfact, pow_one] at h
              exact h
            have hTotal : (Q : Set G).toFinset.card = 13 := by
              rw [Set.toFinset_card]
              exact hQ_card
            have hOneIn : (1 : G) ∈ (Q : Set G).toFinset := by
              rw [Set.mem_toFinset]
              exact (Q : Subgroup G).one_mem
            -- Count non-identity elements: |Q \ {1}| = |Q| - 1 = 12
            simp only [families]
            have herase : (Q : Set G).toFinset.filter (· ≠ 1) = (Q : Set G).toFinset.erase 1 := by
              ext x
              simp only [Finset.mem_filter, Finset.mem_erase, ne_eq]
              tauto
            rw [herase, Finset.card_erase_of_mem hOneIn, hTotal]

          -- The families are pairwise disjoint (from hSylow13_disjoint)
          have hfam_disj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Sylow 13 G))) families := by
            intro Q _ R _ hQR
            rw [Function.onFun, Finset.disjoint_iff_ne]
            intro x hxQ y hyR hxy
            rw [Finset.mem_filter, Set.mem_toFinset] at hxQ hyR
            rw [hxy] at hxQ
            have hx_in_both : y ∈ (Q : Subgroup G) ⊓ R := ⟨hxQ.1, hyR.1⟩
            have hQR_disj := hSylow13_disjoint Q R hQR
            rw [hQR_disj, Subgroup.mem_bot] at hx_in_both
            exact hyR.2 hx_in_both

          -- S13 equals the union of all families
          have hS13_eq : S13 = Finset.univ.biUnion families := by
            ext x
            constructor
            · intro hord
              rw [Finset.mem_filter] at hord
              obtain ⟨Q, hQ⟩ := horder13_in_sylow x hord.2
              rw [Finset.mem_biUnion]
              use Q
              constructor
              · exact Finset.mem_univ Q
              · rw [Finset.mem_filter, Set.mem_toFinset]
                refine ⟨hQ, ?_⟩
                intro h1
                rw [h1] at hord
                simp only [Finset.mem_univ, orderOf_one, true_and] at hord
                exact (by decide : ¬(1 : ℕ) = 13) hord
            · intro hxQ
              rw [Finset.mem_biUnion] at hxQ
              obtain ⟨Q, _, hxQ'⟩ := hxQ
              rw [Finset.mem_filter, Set.mem_toFinset] at hxQ'
              simp only [S13, Finset.mem_filter, Finset.mem_univ, true_and]
              exact hSylow13_order Q x hxQ'.1 hxQ'.2

          -- Count using disjoint union
          rw [hS13_eq]
          rw [Finset.card_biUnion hfam_disj]
          simp only [hfam_card, Finset.sum_const, Finset.card_univ, smul_eq_mul]
          have hcard27 : Fintype.card (Sylow 13 G) = 27 := by
            rw [← Nat.card_eq_fintype_card]; exact hn13_eq27
          simp only [hcard27]

        -- Step 7: |nonS13| = 27
        have hnonS13_card : nonS13.card = 27 := by
          have : S13.card + nonS13.card = 351 := by rw [hG] at hpartition; exact hpartition
          omega

        -- Step 8: Every Sylow 3-subgroup is contained in nonS13
        have hSylow3_subset : ∀ Q : Sylow 3 G, ∀ x ∈ (Q : Subgroup G), x ∈ nonS13 := by
          intro Q x hx
          simp only [nonS13, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hSylow3_order_not_13 Q x hx

        -- Step 9: Each Sylow 3-subgroup has 27 elements (as Fintype.card)
        have hSylow3_card : ∀ Q : Sylow 3 G, Fintype.card Q = 27 := by
          intro Q
          have h := Sylow.card_eq_multiplicity (p := 3) Q
          simp only [Nat.card_eq_fintype_card, hG] at h
          have hfact : (351 : ℕ).factorization 3 = 3 := by native_decide
          simp only [hfact, pow_succ, pow_zero, one_mul] at h
          omega

        -- Step 10: The carrier of any Sylow 3-subgroup equals nonS13
        have hSylow3_eq_nonS13 : ∀ Q : Sylow 3 G, (Q : Set G).toFinset = nonS13 := by
          intro Q
          apply Finset.eq_of_subset_of_card_le
          · intro x hx
            rw [Set.mem_toFinset] at hx
            exact hSylow3_subset Q x hx
          · rw [Set.toFinset_card, hnonS13_card]
            exact le_of_eq (hSylow3_card Q).symm

        -- Step 11: All Sylow 3-subgroups have the same carrier, hence are equal
        have hSylow3_unique : ∀ Q R : Sylow 3 G, Q = R := by
          intro Q R
          have hQ := hSylow3_eq_nonS13 Q
          have hR := hSylow3_eq_nonS13 R
          have hcarrier_eq : (Q : Set G) = (R : Set G) := by
            ext x
            simp only [← Set.mem_toFinset, hQ, hR]
          apply Sylow.ext
          ext x
          constructor
          · intro hxQ
            have : x ∈ (Q : Set G) := hxQ
            rw [hcarrier_eq] at this
            exact this
          · intro hxR
            have : x ∈ (R : Set G) := hxR
            rw [← hcarrier_eq] at this
            exact this

        -- Step 12: n₃ = 1 (all Sylow 3-subgroups are equal)
        have hSubsingleton : Subsingleton (Sylow 3 G) := ⟨hSylow3_unique⟩
        have hn3_eq1' : Nat.card (Sylow 3 G) = 1 :=
          Nat.card_eq_one_iff_unique.mpr ⟨hSubsingleton, ⟨P3⟩⟩

        -- Step 13: Contradiction with h13 : n₃ = 13
        simp only [n3] at h13
        omega
    -- Step 9.5: n₃ = 1, so Sylow 3-subgroup is unique (hence normal)
    have hcardNat3 : Nat.card (Sylow 3 G) = 1 := by simpa [n3] using hn3_eq1
    have hsubsingleton3 : Subsingleton (Sylow 3 G) :=
      (Nat.card_eq_one_iff_unique).1 hcardNat3 |>.1
    have hnormal3 : P3.Normal := by
      letI : Subsingleton (Sylow 3 G) := hsubsingleton3
      exact Sylow.normal_of_subsingleton (p := 3) (G := G) P3
    exact ⟨3, P3, hprime3, hdiv3, hnormal3⟩
