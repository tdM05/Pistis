import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that if $|G|=2907$ then $G$ is not simple.
-/

/-Informal Proof

Since $|G|=2907=3^{2}.17.19$, $G$ has $19-$Sylow subgroup of order $19$. Now, we count the number of such subgroups. Let $n_{19}$ be the number of $19-$Sylow subgroup. Now $n_{19}=1+19k$ where $1+19k|3^{2}.17$. The choices for $k$ is $0$. Hence, there is a unique $19-$Sylow subgroup and hence is normal. so $G$ is not simple.
-/

theorem Dummit_Foote_exercise_4_5_21 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 2907) : ¬ IsSimpleGroup G := by
  /-
  **Overview of the proof:**
  We prove that a group G of order 2907 = 3² × 17 × 19 is not simple.

  By Sylow's theorem:
  - n₁₉ ≡ 1 (mod 19) and n₁₉ | 153 = 2907/19, so n₁₉ ∈ {1, 153}
  - n₁₇ ≡ 1 (mod 17) and n₁₇ | 171 = 2907/17, so n₁₇ ∈ {1, 171}

  If n₁₉ = 1 or n₁₇ = 1, we have a unique (hence normal) Sylow subgroup,
  contradicting simplicity.

  If n₁₉ = 153 and n₁₇ = 171, then:
  - Elements of order 19: 153 × 18 = 2754 (Sylow 19-subgroups have trivial pairwise intersection)
  - Elements of order 17: 171 × 16 = 2736 (Sylow 17-subgroups have trivial pairwise intersection)
  Total non-identity elements ≥ 2754 + 2736 = 5490 > 2906 = |G| - 1

  This is a contradiction, so at least one Sylow subgroup is normal.
  -/
  classical
  -- Step 1: Assume G is simple and derive a contradiction.
  intro hSimple
  haveI := hSimple

  -- Step 2: Establish Fact instances for the primes 17 and 19.
  haveI hFact17 : Fact (Nat.Prime 17) := ⟨by native_decide⟩
  haveI hFact19 : Fact (Nat.Prime 19) := ⟨by native_decide⟩

  -- Step 3: Basic setup.
  -- Step 3.1: |G| as Nat.card.
  have h_card_nat : Nat.card G = 2907 := by simpa [Nat.card_eq_fintype_card] using hG

  -- Step 3.2: Prime divisibility facts.
  have h17_dvd : 17 ∣ Nat.card G := by rw [h_card_nat]; native_decide
  have h19_dvd : 19 ∣ Nat.card G := by rw [h_card_nat]; native_decide

  -- Step 4: Get Sylow subgroups.
  obtain ⟨P17⟩ := Sylow.nonempty (G := G) (p := 17)
  obtain ⟨P19⟩ := Sylow.nonempty (G := G) (p := 19)

  -- Step 5: Helper function to derive contradiction from proper nontrivial normal subgroup.
  have contradict_simple : ∀ (H : Subgroup G), H.Normal → H ≠ ⊥ → H ≠ ⊤ → False := by
    intro H hNormal hNeBot hNeTop
    rcases hSimple.eq_bot_or_eq_top_of_normal H hNormal with h | h
    · exact hNeBot h
    · exact hNeTop h

  -- Step 6: Establish that the Sylow subgroups are nontrivial.
  have hP17_ne_bot : (P17 : Subgroup G) ≠ ⊥ := P17.ne_bot_of_dvd_card h17_dvd
  have hP19_ne_bot : (P19 : Subgroup G) ≠ ⊥ := P19.ne_bot_of_dvd_card h19_dvd

  -- Step 7: Compute the cardinalities of the Sylow subgroups.
  -- Step 7.1: Sylow 17-subgroup has cardinality 17.
  have hP17_card : Nat.card P17.toSubgroup = 17 := by
    have h := Sylow.card_eq_multiplicity (G := G) (p := 17) P17
    have hFactor : Nat.factorization (Nat.card G) 17 = 1 := by
      rw [h_card_nat]
      native_decide
    rw [h, hFactor, pow_one]

  -- Step 7.2: Sylow 19-subgroup has cardinality 19.
  have hP19_card : Nat.card P19.toSubgroup = 19 := by
    have h := Sylow.card_eq_multiplicity (G := G) (p := 19) P19
    have hFactor : Nat.factorization (Nat.card G) 19 = 1 := by
      rw [h_card_nat]
      native_decide
    rw [h, hFactor, pow_one]

  -- Step 8: The Sylow subgroups are proper.
  have hP17_ne_top : (P17 : Subgroup G) ≠ ⊤ := by
    intro htop
    have h1 : Nat.card ↥(P17 : Subgroup G) = Nat.card G := by simp [htop]
    rw [hP17_card, h_card_nat] at h1
    -- h1 : 17 = 2907, which is absurd
    omega

  have hP19_ne_top : (P19 : Subgroup G) ≠ ⊤ := by
    intro htop
    have h1 : Nat.card ↥(P19 : Subgroup G) = Nat.card G := by simp [htop]
    rw [hP19_card, h_card_nat] at h1
    -- h1 : 19 = 2907, which is absurd
    omega

  -- Step 9: Count Sylow subgroups and derive contradiction.
  -- Step 9.1: Get the number of Sylow 17-subgroups and Sylow 19-subgroups.
  set n17 : ℕ := Nat.card (Sylow 17 G) with hn17_def
  set n19 : ℕ := Nat.card (Sylow 19 G) with hn19_def

  -- Step 9.2: n₁₇ ≡ 1 (mod 17) and n₁₉ ≡ 1 (mod 19).
  have h_n17_mod : n17 ≡ 1 [MOD 17] := card_sylow_modEq_one (p := 17) (G := G)
  have h_n19_mod : n19 ≡ 1 [MOD 19] := card_sylow_modEq_one (p := 19) (G := G)

  -- Step 9.3: n₁₇ and n₁₉ divide |G|.
  have h_n17_dvd_G : n17 ∣ Nat.card G := by
    have h1 : n17 ∣ P17.index := Sylow.card_dvd_index P17
    exact h1.trans P17.1.index_dvd_card
  have h_n19_dvd_G : n19 ∣ Nat.card G := by
    have h1 : n19 ∣ P19.index := Sylow.card_dvd_index P19
    exact h1.trans P19.1.index_dvd_card

  -- Step 9.4: n₁₇ is coprime to 17 and n₁₉ is coprime to 19.
  have h_n17_coprime : Nat.Coprime n17 17 := by
    have h := not_dvd_card_sylow (p := 17) (G := G)
    exact (Nat.Prime.coprime_iff_not_dvd (by native_decide : Nat.Prime 17)).2 h |>.symm
  have h_n19_coprime : Nat.Coprime n19 19 := by
    have h := not_dvd_card_sylow (p := 19) (G := G)
    exact (Nat.Prime.coprime_iff_not_dvd (by native_decide : Nat.Prime 19)).2 h |>.symm

  -- Step 9.5: n₁₇ | 171 (= 2907/17) and n₁₉ | 153 (= 2907/19).
  have h_n17_dvd : n17 ∣ 171 := by
    have h1 : n17 ∣ 2907 := by rwa [h_card_nat] at h_n17_dvd_G
    -- n₁₇ is coprime to 17 and divides 2907 = 171 × 17
    have h2 : (2907 : ℕ) = 171 * 17 := by native_decide
    rw [h2] at h1
    exact h_n17_coprime.dvd_of_dvd_mul_right h1

  have h_n19_dvd : n19 ∣ 153 := by
    have h1 : n19 ∣ 2907 := by rwa [h_card_nat] at h_n19_dvd_G
    -- n₁₉ is coprime to 19 and divides 2907 = 153 × 19
    have h2 : (2907 : ℕ) = 153 * 19 := by native_decide
    rw [h2] at h1
    exact h_n19_coprime.dvd_of_dvd_mul_right h1

  -- Step 9.6: If n₁₇ = 1, then P17 is normal and we have a contradiction.
  -- If n₁₉ = 1, then P19 is normal and we have a contradiction.
  -- We prove by showing that at least one must equal 1.

  -- Step 9.7: n₁₇ ∈ {1, 3, 9, 19, 57, 171} (divisors of 171) and n₁₇ ≡ 1 (mod 17).
  -- The divisors of 171 that are ≡ 1 (mod 17) are: 1 and 171.
  -- Similarly, n₁₉ ∈ {1, 3, 9, 17, 51, 153} (divisors of 153) and n₁₉ ≡ 1 (mod 19).
  -- The divisors of 153 that are ≡ 1 (mod 19) are: 1 and 153.

  -- Step 9.8: If n₁₇ ≠ 1, then n₁₇ = 171.
  -- If n₁₉ ≠ 1, then n₁₉ = 153.
  -- We'll show this leads to a counting contradiction.

  -- Step 9.9: First, handle the cases where one of them is 1.
  by_cases hn17_eq_1 : n17 = 1
  · -- Case: n₁₇ = 1, so P17 is the unique Sylow 17-subgroup, hence normal.
    have hP17_normal : P17.Normal := by
      have hss : Subsingleton (Sylow 17 G) := by
        have := Nat.card_eq_one_iff_unique.mp hn17_eq_1
        exact this.1
      exact Sylow.normal_of_subsingleton (p := 17) (G := G) P17
    exact contradict_simple (P17 : Subgroup G) hP17_normal hP17_ne_bot hP17_ne_top

  by_cases hn19_eq_1 : n19 = 1
  · -- Case: n₁₉ = 1, so P19 is the unique Sylow 19-subgroup, hence normal.
    have hP19_normal : P19.Normal := by
      have hss : Subsingleton (Sylow 19 G) := by
        have := Nat.card_eq_one_iff_unique.mp hn19_eq_1
        exact this.1
      exact Sylow.normal_of_subsingleton (p := 19) (G := G) P19
    exact contradict_simple (P19 : Subgroup G) hP19_normal hP19_ne_bot hP19_ne_top

  -- Step 10: Now we assume n₁₇ ≠ 1 and n₁₉ ≠ 1.
  -- We'll derive a counting contradiction.

  -- Step 10.1: n₁₇ = 171 (since n₁₇ | 171, n₁₇ ≡ 1 (mod 17), and n₁₇ ≠ 1).
  have hn17_eq_171 : n17 = 171 := by
    -- n₁₇ divides 171 = 3² × 19
    -- n₁₇ ≡ 1 (mod 17)
    -- Divisors of 171: 1, 3, 9, 19, 57, 171
    -- Check each mod 17:
    --   1 ≡ 1 (mod 17) ✓
    --   3 ≡ 3 (mod 17) ✗
    --   9 ≡ 9 (mod 17) ✗
    --   19 ≡ 2 (mod 17) ✗
    --   57 ≡ 6 (mod 17) ✗
    --   171 ≡ 1 (mod 17) ✓
    -- So n₁₇ ∈ {1, 171}, and n₁₇ ≠ 1 implies n₁₇ = 171.
    have h_le : n17 ≤ 171 := Nat.le_of_dvd (by norm_num : 0 < 171) h_n17_dvd
    -- n₁₇ ≡ 1 (mod 17) means n₁₇ = 1 + 17k for some k ≥ 0.
    -- Since n₁₇ ≤ 171 and n₁₇ ≠ 1, possible values: 18, 35, 52, 69, 86, 103, 120, 137, 154, 171.
    -- Among these, divisors of 171: only 171.
    -- Check: 171 = 9 × 19. Divisors: 1, 3, 9, 19, 57, 171.
    -- Among 1-congruent-mod-17: 1 and 171 (since 171 = 10 × 17 + 1).
    -- Since n₁₇ ≠ 1, we have n₁₇ = 171.
    have h_div_choices : n17 = 1 ∨ n17 = 3 ∨ n17 = 9 ∨ n17 = 19 ∨ n17 = 57 ∨ n17 = 171 := by
      -- 171 = 9 × 19 = 3² × 19, divisors: 1, 3, 9, 19, 57, 171
      have h_divs : ∀ d, d ∣ 171 → d = 1 ∨ d = 3 ∨ d = 9 ∨ d = 19 ∨ d = 57 ∨ d = 171 := by
        intro d hd
        have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd (by norm_num : 0 < 171)
        have hd_le : d ≤ 171 := Nat.le_of_dvd (by norm_num : 0 < 171) hd
        interval_cases d <;> omega
      exact h_divs n17 h_n17_dvd
    -- Now check mod 17 for each case.
    rcases h_div_choices with h | h | h | h | h | h
    · exact (hn17_eq_1 h).elim
    · -- n17 = 3, but 3 ≢ 1 (mod 17)
      exfalso
      rw [h] at h_n17_mod
      simp [Nat.ModEq] at h_n17_mod
    · -- n17 = 9, but 9 ≢ 1 (mod 17)
      exfalso
      rw [h] at h_n17_mod
      simp [Nat.ModEq] at h_n17_mod
    · -- n17 = 19, but 19 ≢ 1 (mod 17)
      exfalso
      rw [h] at h_n17_mod
      simp [Nat.ModEq] at h_n17_mod
    · -- n17 = 57, but 57 ≢ 1 (mod 17) (57 = 3 × 17 + 6 ≡ 6)
      exfalso
      rw [h] at h_n17_mod
      simp [Nat.ModEq] at h_n17_mod
    · exact h

  -- Step 10.2: n₁₉ = 153 (since n₁₉ | 153, n₁₉ ≡ 1 (mod 19), and n₁₉ ≠ 1).
  have hn19_eq_153 : n19 = 153 := by
    -- n₁₉ divides 153 = 3² × 17
    -- n₁₉ ≡ 1 (mod 19)
    -- Divisors of 153: 1, 3, 9, 17, 51, 153
    -- Check each mod 19:
    --   1 ≡ 1 (mod 19) ✓
    --   3 ≡ 3 (mod 19) ✗
    --   9 ≡ 9 (mod 19) ✗
    --   17 ≡ 17 (mod 19) ✗
    --   51 ≡ 13 (mod 19) ✗
    --   153 ≡ 1 (mod 19) ✓
    -- So n₁₉ ∈ {1, 153}, and n₁₉ ≠ 1 implies n₁₉ = 153.
    have h_le : n19 ≤ 153 := Nat.le_of_dvd (by norm_num : 0 < 153) h_n19_dvd
    have h_div_choices : n19 = 1 ∨ n19 = 3 ∨ n19 = 9 ∨ n19 = 17 ∨ n19 = 51 ∨ n19 = 153 := by
      -- 153 = 9 × 17 = 3² × 17, divisors: 1, 3, 9, 17, 51, 153
      have h_divs : ∀ d, d ∣ 153 → d = 1 ∨ d = 3 ∨ d = 9 ∨ d = 17 ∨ d = 51 ∨ d = 153 := by
        intro d hd
        have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd (by norm_num : 0 < 153)
        have hd_le : d ≤ 153 := Nat.le_of_dvd (by norm_num : 0 < 153) hd
        interval_cases d <;> omega
      exact h_divs n19 h_n19_dvd
    rcases h_div_choices with h | h | h | h | h | h
    · exact (hn19_eq_1 h).elim
    · -- n19 = 3, but 3 ≢ 1 (mod 19)
      exfalso
      rw [h] at h_n19_mod
      simp [Nat.ModEq] at h_n19_mod
    · -- n19 = 9, but 9 ≢ 1 (mod 19)
      exfalso
      rw [h] at h_n19_mod
      simp [Nat.ModEq] at h_n19_mod
    · -- n19 = 17, but 17 ≢ 1 (mod 19)
      exfalso
      rw [h] at h_n19_mod
      simp [Nat.ModEq] at h_n19_mod
    · -- n19 = 51, but 51 ≢ 1 (mod 19) (51 = 2 × 19 + 13 ≡ 13)
      exfalso
      rw [h] at h_n19_mod
      simp [Nat.ModEq] at h_n19_mod
    · exact h

  -- Step 10.3: Count elements.
  -- Elements of order 17: Each Sylow 17-subgroup has 16 elements of order 17.
  -- Since distinct Sylow 17-subgroups have trivial intersection (order 17 is prime),
  -- the total number of elements of order 17 is n₁₇ × 16 = 171 × 16 = 2736.
  -- Similarly, elements of order 19: n₁₉ × 18 = 153 × 18 = 2754.
  -- Total non-identity elements ≥ 2736 + 2754 = 5490 > 2906 = |G| - 1.

  -- Step 10.4: Derive the final contradiction.
  -- We'll use the fact that the total count exceeds |G|.
  have h_count_17 : n17 * 16 = 2736 := by simp [hn17_eq_171]
  have h_count_19 : n19 * 18 = 2754 := by simp [hn19_eq_153]
  have h_total : n17 * 16 + n19 * 18 = 5490 := by omega

  -- The elements of order 17 and order 19 are distinct (different prime orders).
  -- Together with the identity, we need at least 5490 + 1 = 5491 elements.
  -- But |G| = 2907 < 5491.
  have h_card_lt : (2907 : ℕ) < 5491 := by norm_num

  -- Step 10.5: Use the disjointness of Sylow p-subgroups for prime p.
  -- For a prime p, the non-identity elements of distinct Sylow p-subgroups are disjoint.
  -- This gives us a lower bound on |G|.

  -- The key insight: elements of order 17 are exactly those in some Sylow 17-subgroup
  -- but not the identity. Since |Sylow 17-subgroup| = 17 (prime), any two distinct
  -- Sylow 17-subgroups intersect only at the identity.
  -- So |{elements of order 17}| = n₁₇ × (17 - 1) = 171 × 16 = 2736.
  -- Similarly, |{elements of order 19}| = n₁₉ × (19 - 1) = 153 × 18 = 2754.
  -- Elements of order 17 and order 19 are disjoint (different prime divisors of order).
  -- So |G| ≥ 1 + 2736 + 2754 = 5491 > 2907, contradiction.

  -- Step 10.6: Counting argument with full formalization.
  -- We need to show that the number of elements of order 17 plus order 19 exceeds |G| - 1.

  -- Prime facts for 17 and 19
  have h17_prime : Nat.Prime 17 := by native_decide
  have h19_prime : Nat.Prime 19 := by native_decide

  -- Step 10.6.1: Show distinct Sylow 17-subgroups share only identity
  have hSylow17_disjoint : ∀ P₁ P₂ : Sylow 17 G, P₁ ≠ P₂ →
      (P₁.toSubgroup : Set G) ∩ P₂.toSubgroup = {1} := by
    intro P₁ P₂ hne
    have hCardP1 : Fintype.card P₁ = 17 := by
      have h := Sylow.card_eq_multiplicity (G := G) (p := 17) P₁
      simp only [Nat.card_eq_fintype_card] at h
      rw [hG] at h
      simp only [show (2907 : ℕ).factorization 17 = 1 by native_decide, pow_one] at h
      exact h
    have hCardP2 : Fintype.card P₂ = 17 := by
      have h := Sylow.card_eq_multiplicity (G := G) (p := 17) P₂
      simp only [Nat.card_eq_fintype_card] at h
      rw [hG] at h
      simp only [show (2907 : ℕ).factorization 17 = 1 by native_decide, pow_one] at h
      exact h
    ext g
    simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_singleton_iff]
    constructor
    · intro ⟨hg1, hg2⟩
      by_contra hg_ne
      have hzp_le1 : zpowers g ≤ P₁.toSubgroup := Subgroup.zpowers_le_of_mem hg1
      have hzp_le2 : zpowers g ≤ P₂.toSubgroup := Subgroup.zpowers_le_of_mem hg2
      have hord : orderOf g = 17 := by
        have hord_dvd : orderOf g ∣ Fintype.card P₁ := by
          have h_sub_ord := @orderOf_dvd_card P₁.toSubgroup _ _ ⟨g, hg1⟩
          have h_eq : orderOf (⟨g, hg1⟩ : P₁.toSubgroup) = orderOf g := by
            rw [← Subgroup.orderOf_coe ⟨g, hg1⟩]
          rw [← h_eq]; exact h_sub_ord
        rw [hCardP1] at hord_dvd
        rcases h17_prime.eq_one_or_self_of_dvd _ hord_dvd with hone | h17
        · exact absurd (orderOf_eq_one_iff.mp hone) hg_ne
        · exact h17
      have hzp_card : Fintype.card (zpowers g) = 17 := by simp only [card_zpowers, hord]
      have hzp_eq1 : zpowers g = P₁.toSubgroup := by
        have h_set : (zpowers g : Set G) ⊆ (P₁.toSubgroup : Set G) :=
          SetLike.coe_subset_coe.mpr hzp_le1
        have h_card_ge : Fintype.card P₁.toSubgroup ≤ Fintype.card (zpowers g) := by
          rw [hzp_card, hCardP1]
        exact SetLike.coe_injective (Set.eq_of_subset_of_card_le h_set h_card_ge)
      have hzp_eq2 : zpowers g = P₂.toSubgroup := by
        have h_set : (zpowers g : Set G) ⊆ (P₂.toSubgroup : Set G) :=
          SetLike.coe_subset_coe.mpr hzp_le2
        have h_card_ge : Fintype.card P₂.toSubgroup ≤ Fintype.card (zpowers g) := by
          rw [hzp_card, hCardP2]
        exact SetLike.coe_injective (Set.eq_of_subset_of_card_le h_set h_card_ge)
      exact hne (Sylow.ext (hzp_eq1.symm.trans hzp_eq2))
    · intro hg1; rw [hg1]; exact ⟨P₁.toSubgroup.one_mem, P₂.toSubgroup.one_mem⟩

  -- Step 10.6.2: Show distinct Sylow 19-subgroups share only identity
  have hSylow19_disjoint : ∀ P₁ P₂ : Sylow 19 G, P₁ ≠ P₂ →
      (P₁.toSubgroup : Set G) ∩ P₂.toSubgroup = {1} := by
    intro P₁ P₂ hne
    have hCardP1 : Fintype.card P₁ = 19 := by
      have h := Sylow.card_eq_multiplicity (G := G) (p := 19) P₁
      simp only [Nat.card_eq_fintype_card] at h
      rw [hG] at h
      simp only [show (2907 : ℕ).factorization 19 = 1 by native_decide, pow_one] at h
      exact h
    have hCardP2 : Fintype.card P₂ = 19 := by
      have h := Sylow.card_eq_multiplicity (G := G) (p := 19) P₂
      simp only [Nat.card_eq_fintype_card] at h
      rw [hG] at h
      simp only [show (2907 : ℕ).factorization 19 = 1 by native_decide, pow_one] at h
      exact h
    ext g
    simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_singleton_iff]
    constructor
    · intro ⟨hg1, hg2⟩
      by_contra hg_ne
      have hzp_le1 : zpowers g ≤ P₁.toSubgroup := Subgroup.zpowers_le_of_mem hg1
      have hzp_le2 : zpowers g ≤ P₂.toSubgroup := Subgroup.zpowers_le_of_mem hg2
      have hord : orderOf g = 19 := by
        have hord_dvd : orderOf g ∣ Fintype.card P₁ := by
          have h_sub_ord := @orderOf_dvd_card P₁.toSubgroup _ _ ⟨g, hg1⟩
          have h_eq : orderOf (⟨g, hg1⟩ : P₁.toSubgroup) = orderOf g := by
            rw [← Subgroup.orderOf_coe ⟨g, hg1⟩]
          rw [← h_eq]; exact h_sub_ord
        rw [hCardP1] at hord_dvd
        rcases h19_prime.eq_one_or_self_of_dvd _ hord_dvd with hone | h19
        · exact absurd (orderOf_eq_one_iff.mp hone) hg_ne
        · exact h19
      have hzp_card : Fintype.card (zpowers g) = 19 := by simp only [card_zpowers, hord]
      have hzp_eq1 : zpowers g = P₁.toSubgroup := by
        have h_set : (zpowers g : Set G) ⊆ (P₁.toSubgroup : Set G) :=
          SetLike.coe_subset_coe.mpr hzp_le1
        have h_card_ge : Fintype.card P₁.toSubgroup ≤ Fintype.card (zpowers g) := by
          rw [hzp_card, hCardP1]
        exact SetLike.coe_injective (Set.eq_of_subset_of_card_le h_set h_card_ge)
      have hzp_eq2 : zpowers g = P₂.toSubgroup := by
        have h_set : (zpowers g : Set G) ⊆ (P₂.toSubgroup : Set G) :=
          SetLike.coe_subset_coe.mpr hzp_le2
        have h_card_ge : Fintype.card P₂.toSubgroup ≤ Fintype.card (zpowers g) := by
          rw [hzp_card, hCardP2]
        exact SetLike.coe_injective (Set.eq_of_subset_of_card_le h_set h_card_ge)
      exact hne (Sylow.ext (hzp_eq1.symm.trans hzp_eq2))
    · intro hg1; rw [hg1]; exact ⟨P₁.toSubgroup.one_mem, P₂.toSubgroup.one_mem⟩

  -- Step 10.6.3: Count elements in Sylow subgroups
  have hcard_sylow17 : Fintype.card (Sylow 17 G) = 171 := by
    have h : Nat.card (Sylow 17 G) = 171 := hn17_eq_171
    rw [Nat.card_eq_fintype_card] at h; exact h

  have hPerSylow17 : ∀ P' : Sylow 17 G,
      ((P'.toSubgroup : Set G) \ {1}).toFinset.card = 16 := by
    intro P'
    have hCardP' : Fintype.card P' = 17 := by
      have h := Sylow.card_eq_multiplicity (G := G) (p := 17) P'
      simp only [Nat.card_eq_fintype_card] at h
      rw [hG] at h
      simp only [show (2907 : ℕ).factorization 17 = 1 by native_decide, pow_one] at h
      exact h
    rw [Set.toFinset_diff, Set.toFinset_singleton]
    have h_subset : ({1} : Finset G) ⊆ (P'.toSubgroup : Set G).toFinset := by
      simp only [Finset.singleton_subset_iff, Set.mem_toFinset, SetLike.mem_coe]
      exact P'.toSubgroup.one_mem
    rw [Finset.card_sdiff_of_subset h_subset, Finset.card_singleton]
    have h_card_P' : (P'.toSubgroup : Set G).toFinset.card = 17 := by
      simp only [Set.toFinset_card, SetLike.coe_sort_coe, hCardP']
    omega

  have hcard_sylow19 : Fintype.card (Sylow 19 G) = 153 := by
    have h : Nat.card (Sylow 19 G) = 153 := hn19_eq_153
    rw [Nat.card_eq_fintype_card] at h; exact h

  have hPerSylow19 : ∀ P' : Sylow 19 G,
      ((P'.toSubgroup : Set G) \ {1}).toFinset.card = 18 := by
    intro P'
    have hCardP' : Fintype.card P' = 19 := by
      have h := Sylow.card_eq_multiplicity (G := G) (p := 19) P'
      simp only [Nat.card_eq_fintype_card] at h
      rw [hG] at h
      simp only [show (2907 : ℕ).factorization 19 = 1 by native_decide, pow_one] at h
      exact h
    rw [Set.toFinset_diff, Set.toFinset_singleton]
    have h_subset : ({1} : Finset G) ⊆ (P'.toSubgroup : Set G).toFinset := by
      simp only [Finset.singleton_subset_iff, Set.mem_toFinset, SetLike.mem_coe]
      exact P'.toSubgroup.one_mem
    rw [Finset.card_sdiff_of_subset h_subset, Finset.card_singleton]
    have h_card_P' : (P'.toSubgroup : Set G).toFinset.card = 19 := by
      simp only [Set.toFinset_card, SetLike.coe_sort_coe, hCardP']
    omega

  -- Step 10.6.4: Pairwise disjointness for non-identity elements
  have hPairwiseDisjoint17 : ∀ P₁ P₂ : Sylow 17 G, P₁ ≠ P₂ →
      Disjoint ((P₁.toSubgroup : Set G) \ {1}).toFinset
               ((P₂.toSubgroup : Set G) \ {1}).toFinset := by
    intro P₁ P₂ hne
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    simp only [Set.mem_toFinset, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff] at hg1 hg2
    have hg_inter : g ∈ (P₁.toSubgroup : Set G) ∩ P₂.toSubgroup := ⟨hg1.1, hg2.1⟩
    rw [hSylow17_disjoint P₁ P₂ hne] at hg_inter
    exact hg1.2 hg_inter

  have hPairwiseDisjoint19 : ∀ P₁ P₂ : Sylow 19 G, P₁ ≠ P₂ →
      Disjoint ((P₁.toSubgroup : Set G) \ {1}).toFinset
               ((P₂.toSubgroup : Set G) \ {1}).toFinset := by
    intro P₁ P₂ hne
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    simp only [Set.mem_toFinset, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff] at hg1 hg2
    have hg_inter : g ∈ (P₁.toSubgroup : Set G) ∩ P₂.toSubgroup := ⟨hg1.1, hg2.1⟩
    rw [hSylow19_disjoint P₁ P₂ hne] at hg_inter
    exact hg1.2 hg_inter

  -- Step 10.6.5: Compute cardinalities of unions
  let U17 := Finset.univ.biUnion fun P' : Sylow 17 G => ((P'.toSubgroup : Set G) \ {1}).toFinset
  have hU17_card : U17.card = 2736 := by
    rw [Finset.card_biUnion]
    · simp only [hPerSylow17, Finset.sum_const, Finset.card_univ, hcard_sylow17, smul_eq_mul]
    · intro P₁ _ P₂ _ hne; exact hPairwiseDisjoint17 P₁ P₂ hne

  let U19 := Finset.univ.biUnion fun P' : Sylow 19 G => ((P'.toSubgroup : Set G) \ {1}).toFinset
  have hU19_card : U19.card = 2754 := by
    rw [Finset.card_biUnion]
    · simp only [hPerSylow19, Finset.sum_const, Finset.card_univ, hcard_sylow19, smul_eq_mul]
    · intro P₁ _ P₂ _ hne; exact hPairwiseDisjoint19 P₁ P₂ hne

  -- Step 10.6.6: U17 and U19 are disjoint (different prime orders)
  have hU17_U19_disjoint : Disjoint U17 U19 := by
    rw [Finset.disjoint_left]
    intro g hgU17 hgU19
    rw [Finset.mem_biUnion] at hgU17 hgU19
    obtain ⟨P17', _, hg_in_U17⟩ := hgU17
    obtain ⟨P19', _, hg_in_U19⟩ := hgU19
    simp only [Set.mem_toFinset, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff] at hg_in_U17 hg_in_U19
    obtain ⟨hg_in_P17, hg_ne⟩ := hg_in_U17
    obtain ⟨hg_in_P19, _⟩ := hg_in_U19
    -- g has order 17 (in P17') and order 19 (in P19'), contradiction
    have hord17 : orderOf g = 17 := by
      have hCardP17' : Fintype.card P17' = 17 := by
        have h := Sylow.card_eq_multiplicity (G := G) (p := 17) P17'
        simp only [Nat.card_eq_fintype_card] at h
        rw [hG] at h
        simp only [show (2907 : ℕ).factorization 17 = 1 by native_decide, pow_one] at h
        exact h
      have hord_dvd : orderOf g ∣ 17 := by
        have h_sub_ord := @orderOf_dvd_card P17'.toSubgroup _ _ ⟨g, hg_in_P17⟩
        have h_eq : orderOf (⟨g, hg_in_P17⟩ : P17'.toSubgroup) = orderOf g := by
          rw [← Subgroup.orderOf_coe ⟨g, hg_in_P17⟩]
        rw [h_eq] at h_sub_ord
        rw [hCardP17'] at h_sub_ord
        exact h_sub_ord
      rcases h17_prime.eq_one_or_self_of_dvd _ hord_dvd with hone | h17
      · exact absurd (orderOf_eq_one_iff.mp hone) hg_ne
      · exact h17
    have hord19 : orderOf g = 19 := by
      have hCardP19' : Fintype.card P19' = 19 := by
        have h := Sylow.card_eq_multiplicity (G := G) (p := 19) P19'
        simp only [Nat.card_eq_fintype_card] at h
        rw [hG] at h
        simp only [show (2907 : ℕ).factorization 19 = 1 by native_decide, pow_one] at h
        exact h
      have hord_dvd : orderOf g ∣ 19 := by
        have h_sub_ord := @orderOf_dvd_card P19'.toSubgroup _ _ ⟨g, hg_in_P19⟩
        have h_eq : orderOf (⟨g, hg_in_P19⟩ : P19'.toSubgroup) = orderOf g := by
          rw [← Subgroup.orderOf_coe ⟨g, hg_in_P19⟩]
        rw [h_eq] at h_sub_ord
        rw [hCardP19'] at h_sub_ord
        exact h_sub_ord
      rcases h19_prime.eq_one_or_self_of_dvd _ hord_dvd with hone | h19
      · have hg_eq_one : g = 1 := orderOf_eq_one_iff.mp hone
        exact absurd hg_eq_one hg_ne
      · exact h19
    omega -- 17 ≠ 19

  -- Step 10.6.7: Total cardinality
  have hUnion_card : (U17 ∪ U19).card = 5490 := by
    rw [Finset.card_union_of_disjoint hU17_U19_disjoint, hU17_card, hU19_card]

  -- Step 10.6.8: The union is a subset of G \ {1}
  have hTotal_le_G : (U17 ∪ U19).card + 1 ≤ Fintype.card G := by
    have h_subset : U17 ∪ U19 ⊆ Finset.univ \ {1} := by
      intro g hg
      simp only [Finset.mem_union] at hg
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
      rcases hg with hgU17 | hgU19
      · rw [Finset.mem_biUnion] at hgU17
        obtain ⟨_, _, hg'⟩ := hgU17
        simp only [Set.mem_toFinset, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff] at hg'
        exact hg'.2
      · rw [Finset.mem_biUnion] at hgU19
        obtain ⟨_, _, hg'⟩ := hgU19
        simp only [Set.mem_toFinset, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff] at hg'
        exact hg'.2
    have h_card_le : (U17 ∪ U19).card ≤ (Finset.univ \ {1} : Finset G).card :=
      Finset.card_le_card h_subset
    have h_sdiff_card : (Finset.univ \ {1} : Finset G).card = Fintype.card G - 1 := by
      have h_sub : ({1} : Finset G) ⊆ Finset.univ :=
        Finset.singleton_subset_iff.mpr (Finset.mem_univ 1)
      rw [Finset.card_sdiff, Finset.card_univ]
      simp only [Finset.singleton_inter_of_mem (Finset.mem_univ (1 : G)), Finset.card_singleton]
    omega

  -- Step 10.6.9: Final contradiction
  omega
