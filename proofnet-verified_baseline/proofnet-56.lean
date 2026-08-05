import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that if $|G|=132$ then $G$ is not simple.
-/

/-Informal Proof

Since $|G|=132=2^{2}.3.11$, $G$ has $2-$Sylow subgroup of order $4$, as well as $11-$Sylow subgroup of order $11$, and $3-$Sylow subgroup of order $3$. Now, we count the number of such subgroups. Let $n_{11}$ be the number of  $11-$Sylow subgroup and $n_{3}$ be the number of  $3-$Sylow subgroup. Now $n_{11}=1+11k$ where $1+11k|12$. The choices for $k$ are $0$ or $1$. If $k=0$, there is only one $11-$Sylow subgroup and hence normal. So, assume now, that there are $12$ $11-$Sylow subgroup(for $k=1$). Now we look at $3-$ Sylow subgroups. $n_{3}=1+3k| 44$. So choice for $k$ are $0$, $1$, and $7$. If $k=0$, there is only one $3-$Sylow subgroup and hence normal. So, assume now, that there are $4$ $2-$Sylow subgroup (for $k=3$). Now we claim that simultaneously, there cannot be $12$ $11-$Sylow subgroup and $4$ $3-$Sylow subgroups provided there is more than one $2-$Sylow subgroups. So, either $2-$Sylow subgroup is normal or if not, then, either $11-$Sylow subgroup is normal being unique, or  the $3-$Sylow subgroup is normal(We don't consider the possibility of $22$ $3-$Sylow subgroup because of obvious reason). Now, to prove the claim, we observe that there are $120$ elements of order $11$. Also there are $8$ elements of order $3$. So we already get $120+8+1=129$ distinct elements in the group. Let us count the number of $2-$Sylow subgroups in $G$. $n_{2}=1+2k|33$. The possibilities for $k$ are $0$, $1$, $5$, $16$. Now, assume there is more than one $2-$Sylow subgroups. Let $H_{1}$ and $H_{2}$ be two distinct  $2-$Sylow subgroup. Now $|H_{1}|=4$. So we already get $129+3=132$ distinct elements in the group. Now $H_{2}$ being distinct from $H_{1}$, has at least one element which is not in $H_{1}$. This adds one more element in the group, at the least. Now already we have number of elements in the group exceeding the number of element in $G$. This gives a contradiction and proves the claim.
Hence $G$ is not simple.
-/

theorem Dummit_Foote_exercise_4_5_22 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 132) : ¬ IsSimpleGroup G := by
  classical
  -- Step 0: Argue by contradiction; assume G is simple.
  intro hSimple
  haveI : IsSimpleGroup G := hSimple

  -- Step 1: Basic setup.
  -- Step 1.1: Translate |G| = 132 to Nat.card.
  have h_card_nat : Nat.card G = 132 := by simpa [Nat.card_eq_fintype_card] using hG

  -- Step 1.2: Key divisibility facts about 132 = 2² × 3 × 11.
  have h_prime11 : Nat.Prime 11 := by decide
  have h_prime3 : Nat.Prime 3 := by decide
  have h_prime2 : Nat.Prime 2 := by decide
  haveI : Fact (Nat.Prime 11) := ⟨h_prime11⟩
  haveI : Fact (Nat.Prime 3) := ⟨h_prime3⟩
  haveI : Fact (Nat.Prime 2) := ⟨h_prime2⟩

  -- Step 1.3: Divisibility proofs for primes dividing 132.
  have h_dvd_11 : 11 ∣ Nat.card G := by rw [h_card_nat]; decide
  have h_dvd_3 : 3 ∣ Nat.card G := by rw [h_card_nat]; decide
  have h_dvd_2 : 2 ∣ Nat.card G := by rw [h_card_nat]; decide

  -- Step 1.4: Non-divisibility proofs for higher powers.
  have h_not_dvd_121 : ¬ 11 ^ 2 ∣ Nat.card G := by rw [h_card_nat]; decide
  have h_not_dvd_9 : ¬ 3 ^ 2 ∣ Nat.card G := by rw [h_card_nat]; decide
  have h_not_dvd_8 : ¬ 2 ^ 3 ∣ Nat.card G := by rw [h_card_nat]; decide

  -- Step 2: Get Sylow subgroups.
  obtain ⟨P⟩ := Sylow.nonempty (G := G) (p := 11)
  obtain ⟨Q⟩ := Sylow.nonempty (G := G) (p := 3)
  obtain ⟨R⟩ := Sylow.nonempty (G := G) (p := 2)

  -- Step 3: Analyze the number of Sylow-11 subgroups.
  -- n₁₁ ≡ 1 (mod 11) and n₁₁ | 12. So n₁₁ ∈ {1, 12}.
  set n11 : ℕ := Nat.card (Sylow 11 G) with hn11_def
  have h_n11_mod : n11 ≡ 1 [MOD 11] := card_sylow_modEq_one (p := 11) (G := G)
  have h_n11_coprime : Nat.Coprime n11 11 := by
    have h := not_dvd_card_sylow (p := 11) (G := G)
    exact (h_prime11.coprime_iff_not_dvd).2 h |>.symm

  -- Step 3.1: Show n₁₁ | 12 using Sylow index divisibility.
  have h_n11_dvd : n11 ∣ 12 := by
    have h1 : n11 ∣ Nat.card G := by
      have h2 : n11 ∣ P.index := Sylow.card_dvd_index P
      exact h2.trans P.1.index_dvd_card
    have h3 : n11 ∣ 11 * 12 := by
      rw [h_card_nat] at h1
      exact h1
    exact h_n11_coprime.dvd_of_dvd_mul_left h3

  -- Step 3.2: n₁₁ ∈ {1, 12} by checking divisors of 12 against mod 11 constraint.
  have h_n11_le : n11 ≤ 12 := Nat.le_of_dvd (by decide) h_n11_dvd
  have h_n11_pos : 0 < n11 := Nat.card_pos
  have h_n11_cases : n11 = 1 ∨ n11 = 12 := by
    have hdiv : n11 ∈ Nat.divisors 12 := Nat.mem_divisors.2 ⟨h_n11_dvd, by decide⟩
    have : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by decide
    rw [this] at hdiv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
    rcases hdiv with h1 | h2 | h3 | h4 | h5 | h6
    · left; exact h1
    · exfalso; simp only [Nat.ModEq, h2] at h_n11_mod; omega
    · exfalso; simp only [Nat.ModEq, h3] at h_n11_mod; omega
    · exfalso; simp only [Nat.ModEq, h4] at h_n11_mod; omega
    · exfalso; simp only [Nat.ModEq, h5] at h_n11_mod; omega
    · right; exact h6

  -- Step 4: Helper to show a proper nontrivial normal subgroup contradicts simplicity.
  have contradict_simple : ∀ (H : Subgroup G), H.Normal → H ≠ ⊥ → H ≠ ⊤ → False := by
    intro H hNormal hNeBot hNeTop
    rcases hSimple.eq_bot_or_eq_top_of_normal H hNormal with h | h
    · exact hNeBot h
    · exact hNeTop h

  -- Step 4.1: Helper for Sylow-11 subgroup: |S| = 11 < 132, so S ≠ G.
  have sylow11_ne_top : (P : Subgroup G) ≠ ⊤ := by
    intro htop
    have h1 : Nat.card ↥(P : Subgroup G) = Nat.card G := by simp [htop]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
    have h2 : 11 ^ k ∣ Nat.card G := by rw [← hk]; exact P.1.card_subgroup_dvd_card
    have h3 : k ≤ 1 := by
      by_contra hk_gt
      push_neg at hk_gt
      have : 11 ^ 2 ∣ 11 ^ k := pow_dvd_pow 11 hk_gt
      exact h_not_dvd_121 (this.trans h2)
    have h4 : Nat.card ↥(P : Subgroup G) ≤ 11 := by
      calc Nat.card ↥(P : Subgroup G) = 11 ^ k := hk
        _ ≤ 11 ^ 1 := Nat.pow_le_pow_right (by decide) h3
        _ = 11 := pow_one 11
    rw [h1, h_card_nat] at h4
    omega

  -- Step 4.2: Helper for Sylow-3 subgroup: |S| = 3 < 132, so S ≠ G.
  have sylow3_ne_top : (Q : Subgroup G) ≠ ⊤ := by
    intro htop
    have h1 : Nat.card ↥(Q : Subgroup G) = Nat.card G := by simp [htop]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp Q.isPGroup'
    have h2 : 3 ^ k ∣ Nat.card G := by rw [← hk]; exact Q.1.card_subgroup_dvd_card
    have h3 : k ≤ 1 := by
      by_contra hk_gt
      push_neg at hk_gt
      have : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 hk_gt
      exact h_not_dvd_9 (this.trans h2)
    have h4 : Nat.card ↥(Q : Subgroup G) ≤ 3 := by
      calc Nat.card ↥(Q : Subgroup G) = 3 ^ k := hk
        _ ≤ 3 ^ 1 := Nat.pow_le_pow_right (by decide) h3
        _ = 3 := pow_one 3
    rw [h1, h_card_nat] at h4
    omega

  -- Step 4.2: For Sylow-2, we have 2^2 | 132 but 2^3 ∤ 132, so |Sylow 2-subgroup| = 4.
  have sylow2_ne_top : (R : Subgroup G) ≠ ⊤ := by
    intro htop
    have h1 : Nat.card ↥(R : Subgroup G) = Nat.card G := by simp [htop]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp R.isPGroup'
    have h2 : 2 ^ k ∣ Nat.card G := by rw [← hk]; exact R.1.card_subgroup_dvd_card
    have h3 : k ≤ 2 := by
      by_contra hk_gt
      push_neg at hk_gt
      have : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 hk_gt
      exact h_not_dvd_8 (this.trans h2)
    have h4 : Nat.card ↥(R : Subgroup G) ≤ 4 := by
      calc Nat.card ↥(R : Subgroup G) = 2 ^ k := hk
        _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) h3
        _ = 4 := by decide
    rw [h1, h_card_nat] at h4
    omega

  -- Step 5: Case analysis on n₁₁.
  rcases h_n11_cases with hn11_1 | hn11_12

  -- Case 1: n₁₁ = 1 → unique Sylow-11 subgroup → normal → contradiction.
  · have h : Nat.card (Sylow 11 G) = 1 := hn11_1
    have hss : Subsingleton (Sylow 11 G) := (Nat.card_eq_one_iff_unique.1 h).1
    haveI : Subsingleton (Sylow 11 G) := hss
    have hP_normal : P.Normal := Sylow.normal_of_subsingleton (p := 11) (G := G) P
    have hP_ne_bot : (P : Subgroup G) ≠ ⊥ := P.ne_bot_of_dvd_card h_dvd_11
    have hP_ne_top : (P : Subgroup G) ≠ ⊤ := sylow11_ne_top
    exact contradict_simple (P : Subgroup G) hP_normal hP_ne_bot hP_ne_top

  -- Case 2: n₁₁ = 12 → analyze Sylow-3 subgroups.
  · -- Step 6: Analyze Sylow-3 subgroups.
    -- n₃ ≡ 1 (mod 3) and n₃ | 44. So n₃ ∈ {1, 4, 22}.
    set n3 : ℕ := Nat.card (Sylow 3 G) with hn3_def
    have h_n3_mod : n3 ≡ 1 [MOD 3] := card_sylow_modEq_one (p := 3) (G := G)
    have h_n3_coprime : Nat.Coprime n3 3 := by
      have h := not_dvd_card_sylow (p := 3) (G := G)
      exact (h_prime3.coprime_iff_not_dvd).2 h |>.symm

    -- Step 6.1: Show n₃ | 44.
    have h_n3_dvd : n3 ∣ 44 := by
      have h1 : n3 ∣ Nat.card G := by
        have h2 : n3 ∣ Q.index := Sylow.card_dvd_index Q
        exact h2.trans Q.1.index_dvd_card
      have h3 : n3 ∣ 3 * 44 := by
        rw [h_card_nat] at h1
        exact h1
      exact h_n3_coprime.dvd_of_dvd_mul_left h3

    -- Step 6.2: n₃ ∈ {1, 4, 22} (divisors of 44 that are ≡ 1 (mod 3)).
    have h_n3_le : n3 ≤ 44 := Nat.le_of_dvd (by decide) h_n3_dvd
    have h_n3_pos : 0 < n3 := Nat.card_pos
    have h_n3_cases : n3 = 1 ∨ n3 = 4 ∨ n3 = 22 := by
      have hdiv : n3 ∈ Nat.divisors 44 := Nat.mem_divisors.2 ⟨h_n3_dvd, by decide⟩
      have : Nat.divisors 44 = {1, 2, 4, 11, 22, 44} := by decide
      rw [this] at hdiv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
      rcases hdiv with h1 | h2 | h3 | h4 | h5 | h6
      · left; exact h1
      · exfalso; simp only [Nat.ModEq, h2] at h_n3_mod; omega
      · right; left; exact h3
      · exfalso; simp only [Nat.ModEq, h4] at h_n3_mod; omega
      · right; right; exact h5
      · exfalso; simp only [Nat.ModEq, h6] at h_n3_mod; omega

    rcases h_n3_cases with hn3_1 | hn3_4 | hn3_22

    -- Case 2.1: n₃ = 1 → unique Sylow-3 subgroup → normal → contradiction.
    · have h : Nat.card (Sylow 3 G) = 1 := hn3_1
      have hss : Subsingleton (Sylow 3 G) := (Nat.card_eq_one_iff_unique.1 h).1
      haveI : Subsingleton (Sylow 3 G) := hss
      have hQ_normal : Q.Normal := Sylow.normal_of_subsingleton (p := 3) (G := G) Q
      have hQ_ne_bot : (Q : Subgroup G) ≠ ⊥ := Q.ne_bot_of_dvd_card h_dvd_3
      have hQ_ne_top : (Q : Subgroup G) ≠ ⊤ := sylow3_ne_top
      exact contradict_simple (Q : Subgroup G) hQ_normal hQ_ne_bot hQ_ne_top

    -- Case 2.2: n₃ = 4 → analyze Sylow-2 subgroups.
    · -- Step 7: Analyze Sylow-2 subgroups.
      -- n₂ ≡ 1 (mod 2) (odd) and n₂ | 33. So n₂ ∈ {1, 3, 11, 33}.
      set n2 : ℕ := Nat.card (Sylow 2 G) with hn2_def
      have h_n2_coprime : Nat.Coprime n2 2 := by
        have h := not_dvd_card_sylow (p := 2) (G := G)
        exact (h_prime2.coprime_iff_not_dvd).2 h |>.symm

      -- Step 7.1: Show n₂ | 33.
      have h_n2_dvd : n2 ∣ 33 := by
        have h1 : n2 ∣ Nat.card G := by
          have h2 : n2 ∣ R.index := Sylow.card_dvd_index R
          exact h2.trans R.1.index_dvd_card
        have h3 : n2 ∣ 4 * 33 := by
          rw [h_card_nat] at h1
          exact h1
        have h4 : Nat.Coprime n2 4 := by
          have : Nat.Coprime n2 (2 ^ 2) := h_n2_coprime.pow_right 2
          simp only [pow_two] at this
          exact this
        exact h4.dvd_of_dvd_mul_left h3

      -- Step 7.2: n₂ ∈ {1, 3, 11, 33}.
      have h_n2_le : n2 ≤ 33 := Nat.le_of_dvd (by decide) h_n2_dvd
      have h_n2_pos : 0 < n2 := Nat.card_pos
      have h_n2_cases : n2 = 1 ∨ n2 = 3 ∨ n2 = 11 ∨ n2 = 33 := by
        have hdiv : n2 ∈ Nat.divisors 33 := Nat.mem_divisors.2 ⟨h_n2_dvd, by decide⟩
        have : Nat.divisors 33 = {1, 3, 11, 33} := by decide
        rw [this] at hdiv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
        rcases hdiv with h1 | h2 | h3 | h4
        · left; exact h1
        · right; left; exact h2
        · right; right; left; exact h3
        · right; right; right; exact h4

      rcases h_n2_cases with hn2_1 | hn2_3 | hn2_11 | hn2_33

      -- Case 2.2.1: n₂ = 1 → unique Sylow-2 subgroup → normal → contradiction.
      · have h : Nat.card (Sylow 2 G) = 1 := hn2_1
        have hss : Subsingleton (Sylow 2 G) := (Nat.card_eq_one_iff_unique.1 h).1
        haveI : Subsingleton (Sylow 2 G) := hss
        have hR_normal : R.Normal := Sylow.normal_of_subsingleton (p := 2) (G := G) R
        have hR_ne_bot : (R : Subgroup G) ≠ ⊥ := R.ne_bot_of_dvd_card h_dvd_2
        exact contradict_simple (R : Subgroup G) hR_normal hR_ne_bot sylow2_ne_top

      -- Case 2.2.2: n₂ = 3 → G embeds into S₃ via quotient action.
      -- |G| | 3! = 6, but 132 ∤ 6. Contradiction!
      · -- Step 8.1: The normalizer of R has index n₂ = 3 in G.
        have h_idx : R.1.normalizer.index = n2 := by
          rw [← Sylow.card_eq_index_normalizer R]
        -- Step 8.2: The normalCore of the normalizer is trivial (for a simple group).
        have h_core_bot : R.1.normalizer.normalCore = ⊥ := by
          have hN : R.1.normalizer.normalCore.Normal := R.1.normalizer.normalCore_normal
          rcases hSimple.eq_bot_or_eq_top_of_normal _ hN with h | h
          · exact h
          · exfalso
            have h1 : R.1.normalizer = ⊤ := by
              apply le_antisymm le_top
              rw [← h]
              exact Subgroup.normalCore_le _
            have h2 : (R : Subgroup G).Normal := Subgroup.normalizer_eq_top_iff.1 h1
            haveI : (R : Subgroup G).Normal := h2
            haveI hUniq : Unique (Sylow 2 G) := Sylow.unique_of_normal R h2
            have h3 : Nat.card (Sylow 2 G) = 1 := Nat.card_eq_one_iff_unique.2 ⟨Unique.instSubsingleton, ⟨R⟩⟩
            omega
        -- Step 8.3: G acts on G/N_G(R) by left multiplication, inducing a homomorphism to S_n₂.
        -- The kernel is normalCore(N_G(R)) = ⊥, so this is injective.
        -- Thus |G| divides |S_n₂| = n₂!.
        have h_divides : Nat.card G ∣ Nat.factorial n2 := by
          -- Identify normalCore with kernel of the permutation action.
          have hKer :
              R.1.normalizer.normalCore = (MulAction.toPermHom G (G ⧸ R.1.normalizer)).ker := by
            simp [Subgroup.normalCore_eq_ker (H := R.1.normalizer)]
          -- Relate index of kernel to size of image.
          have hIndexKer :
              R.1.normalizer.normalCore.index =
                Nat.card (MulAction.toPermHom G (G ⧸ R.1.normalizer)).range := by
            simpa [hKer] using index_ker (MulAction.toPermHom G (G ⧸ R.1.normalizer))
          -- The image sits inside the full symmetric group.
          have hRangeDiv :
              Nat.card (MulAction.toPermHom G (G ⧸ R.1.normalizer)).range ∣
                Nat.card (Equiv.Perm (G ⧸ R.1.normalizer)) :=
            card_subgroup_dvd_card _
          have hDiv1 :
              R.1.normalizer.normalCore.index ∣ Nat.card (Equiv.Perm (G ⧸ R.1.normalizer)) := by
            simp only [hIndexKer]
            exact hRangeDiv
          have hPermCardNat :
              Nat.card (Equiv.Perm (G ⧸ R.1.normalizer)) =
                Nat.factorial (Nat.card (G ⧸ R.1.normalizer)) :=
            Nat.card_perm (α := G ⧸ R.1.normalizer)
          have hDiv2 :
              R.1.normalizer.normalCore.index ∣ Nat.factorial (Nat.card (G ⧸ R.1.normalizer)) := by
            exact hPermCardNat ▸ hDiv1
          have hIndexCardNat : Nat.card (G ⧸ R.1.normalizer) = R.1.normalizer.index :=
            (Subgroup.index_eq_card (H := R.1.normalizer)).symm
          have hDiv3 : R.1.normalizer.normalCore.index ∣ Nat.factorial R.1.normalizer.index := by
            exact hIndexCardNat ▸ hDiv2
          -- Since normalCore = ⊥, its index is |G|.
          have hCoreIdx : R.1.normalizer.normalCore.index = Nat.card G := by
            rw [h_core_bot]
            exact Subgroup.index_bot
          -- Substitute: normalCore.index = |G| and normalizer.index = n2.
          calc Nat.card G = R.1.normalizer.normalCore.index := hCoreIdx.symm
            _ ∣ Nat.factorial R.1.normalizer.index := hDiv3
            _ = Nat.factorial n2 := by rw [h_idx]
        rw [h_card_nat, hn2_3] at h_divides
        -- 132 ∤ 3! = 6
        norm_num at h_divides

      -- Case 2.2.3: n₂ = 11 → use embedding into S₃ via Sylow-3 action.
      -- Since n₃ = 4, the Sylow-3 normalizer has index 4 in G.
      -- If the normalCore is ⊥ (simple group), G embeds into S₄.
      -- But |G| = 132 does not divide |S₄| = 24. Contradiction!
      · -- Step 8.1: The normalizer of Q has index n₃ = 4 in G.
        have h_idx_Q : Q.1.normalizer.index = n3 := by
          rw [← Sylow.card_eq_index_normalizer Q]
        -- Step 8.2: The normalCore of the normalizer is trivial (for a simple group).
        have h_core_bot_Q : Q.1.normalizer.normalCore = ⊥ := by
          have hN : Q.1.normalizer.normalCore.Normal := Q.1.normalizer.normalCore_normal
          rcases hSimple.eq_bot_or_eq_top_of_normal _ hN with h | h
          · exact h
          · exfalso
            have h1 : Q.1.normalizer = ⊤ := by
              apply le_antisymm le_top
              rw [← h]
              exact Subgroup.normalCore_le _
            have h2 : (Q : Subgroup G).Normal := Subgroup.normalizer_eq_top_iff.1 h1
            haveI : (Q : Subgroup G).Normal := h2
            haveI hUniq : Unique (Sylow 3 G) := Sylow.unique_of_normal Q h2
            have h3 : Nat.card (Sylow 3 G) = 1 := Nat.card_eq_one_iff_unique.2 ⟨Unique.instSubsingleton, ⟨Q⟩⟩
            omega
        -- Step 8.3: G acts on G/N_G(Q) by left multiplication, inducing a homomorphism to S_n₃.
        -- The kernel is normalCore(N_G(Q)) = ⊥, so this is injective.
        -- Thus |G| divides |S_n₃| = n₃!.
        have h_divides_Q : Nat.card G ∣ Nat.factorial n3 := by
          -- Identify normalCore with kernel of the permutation action.
          have hKer :
              Q.1.normalizer.normalCore = (MulAction.toPermHom G (G ⧸ Q.1.normalizer)).ker := by
            simp [Subgroup.normalCore_eq_ker (H := Q.1.normalizer)]
          -- Relate index of kernel to size of image.
          have hIndexKer :
              Q.1.normalizer.normalCore.index =
                Nat.card (MulAction.toPermHom G (G ⧸ Q.1.normalizer)).range := by
            simpa [hKer] using index_ker (MulAction.toPermHom G (G ⧸ Q.1.normalizer))
          -- The image sits inside the full symmetric group.
          have hRangeDiv :
              Nat.card (MulAction.toPermHom G (G ⧸ Q.1.normalizer)).range ∣
                Nat.card (Equiv.Perm (G ⧸ Q.1.normalizer)) :=
            card_subgroup_dvd_card _
          have hDiv1 :
              Q.1.normalizer.normalCore.index ∣ Nat.card (Equiv.Perm (G ⧸ Q.1.normalizer)) := by
            simp only [hIndexKer]
            exact hRangeDiv
          have hPermCardNat :
              Nat.card (Equiv.Perm (G ⧸ Q.1.normalizer)) =
                Nat.factorial (Nat.card (G ⧸ Q.1.normalizer)) :=
            Nat.card_perm (α := G ⧸ Q.1.normalizer)
          have hDiv2 :
              Q.1.normalizer.normalCore.index ∣ Nat.factorial (Nat.card (G ⧸ Q.1.normalizer)) := by
            exact hPermCardNat ▸ hDiv1
          have hIndexCardNat : Nat.card (G ⧸ Q.1.normalizer) = Q.1.normalizer.index :=
            (Subgroup.index_eq_card (H := Q.1.normalizer)).symm
          have hDiv3 : Q.1.normalizer.normalCore.index ∣ Nat.factorial Q.1.normalizer.index := by
            exact hIndexCardNat ▸ hDiv2
          -- Since normalCore = ⊥, its index is |G|.
          have hCoreIdx : Q.1.normalizer.normalCore.index = Nat.card G := by
            rw [h_core_bot_Q]
            exact Subgroup.index_bot
          -- Substitute: normalCore.index = |G| and normalizer.index = n3.
          calc Nat.card G = Q.1.normalizer.normalCore.index := hCoreIdx.symm
            _ ∣ Nat.factorial Q.1.normalizer.index := hDiv3
            _ = Nat.factorial n3 := by rw [h_idx_Q]
        rw [h_card_nat, hn3_4] at h_divides_Q
        -- 132 ∤ 4! = 24
        norm_num at h_divides_Q

      -- Case 2.2.4: n₂ = 33 → use embedding into S₄ via Sylow-3 action.
      -- Since n₃ = 4, the Sylow-3 normalizer has index 4 in G.
      -- If the normalCore is ⊥ (simple group), G embeds into S₄.
      -- But |G| = 132 does not divide |S₄| = 24. Contradiction!
      · -- Step 9.1: The normalizer of Q has index n₃ = 4 in G.
        have h_idx_Q : Q.1.normalizer.index = n3 := by
          rw [← Sylow.card_eq_index_normalizer Q]
        -- Step 9.2: The normalCore of the normalizer is trivial (for a simple group).
        have h_core_bot_Q : Q.1.normalizer.normalCore = ⊥ := by
          have hN : Q.1.normalizer.normalCore.Normal := Q.1.normalizer.normalCore_normal
          rcases hSimple.eq_bot_or_eq_top_of_normal _ hN with h | h
          · exact h
          · exfalso
            have h1 : Q.1.normalizer = ⊤ := by
              apply le_antisymm le_top
              rw [← h]
              exact Subgroup.normalCore_le _
            have h2 : (Q : Subgroup G).Normal := Subgroup.normalizer_eq_top_iff.1 h1
            haveI : (Q : Subgroup G).Normal := h2
            haveI hUniq : Unique (Sylow 3 G) := Sylow.unique_of_normal Q h2
            have h3 : Nat.card (Sylow 3 G) = 1 := Nat.card_eq_one_iff_unique.2 ⟨Unique.instSubsingleton, ⟨Q⟩⟩
            omega
        -- Step 9.3: G acts on G/N_G(Q), inducing an injection G → S₄.
        -- Thus |G| divides 4! = 24.
        have h_divides_Q : Nat.card G ∣ Nat.factorial n3 := by
          have hKer :
              Q.1.normalizer.normalCore = (MulAction.toPermHom G (G ⧸ Q.1.normalizer)).ker := by
            simp [Subgroup.normalCore_eq_ker (H := Q.1.normalizer)]
          have hIndexKer :
              Q.1.normalizer.normalCore.index =
                Nat.card (MulAction.toPermHom G (G ⧸ Q.1.normalizer)).range := by
            simpa [hKer] using index_ker (MulAction.toPermHom G (G ⧸ Q.1.normalizer))
          have hRangeDiv :
              Nat.card (MulAction.toPermHom G (G ⧸ Q.1.normalizer)).range ∣
                Nat.card (Equiv.Perm (G ⧸ Q.1.normalizer)) :=
            card_subgroup_dvd_card _
          have hDiv1 :
              Q.1.normalizer.normalCore.index ∣ Nat.card (Equiv.Perm (G ⧸ Q.1.normalizer)) := by
            simp only [hIndexKer]
            exact hRangeDiv
          have hPermCardNat :
              Nat.card (Equiv.Perm (G ⧸ Q.1.normalizer)) =
                Nat.factorial (Nat.card (G ⧸ Q.1.normalizer)) :=
            Nat.card_perm (α := G ⧸ Q.1.normalizer)
          have hDiv2 :
              Q.1.normalizer.normalCore.index ∣ Nat.factorial (Nat.card (G ⧸ Q.1.normalizer)) := by
            exact hPermCardNat ▸ hDiv1
          have hIndexCardNat : Nat.card (G ⧸ Q.1.normalizer) = Q.1.normalizer.index :=
            (Subgroup.index_eq_card (H := Q.1.normalizer)).symm
          have hDiv3 : Q.1.normalizer.normalCore.index ∣ Nat.factorial Q.1.normalizer.index := by
            exact hIndexCardNat ▸ hDiv2
          have hCoreIdx : Q.1.normalizer.normalCore.index = Nat.card G := by
            rw [h_core_bot_Q]
            exact Subgroup.index_bot
          calc Nat.card G = Q.1.normalizer.normalCore.index := hCoreIdx.symm
            _ ∣ Nat.factorial Q.1.normalizer.index := hDiv3
            _ = Nat.factorial n3 := by rw [h_idx_Q]
        rw [h_card_nat, hn3_4] at h_divides_Q
        -- 132 ∤ 4! = 24
        norm_num at h_divides_Q

    -- Case 2.3: n₃ = 22 → element counting contradiction.
    -- 12 Sylow-11 give 12 × 10 = 120 elements of order 11.
    -- 22 Sylow-3 give 22 × 2 = 44 elements of order 3.
    -- 120 + 44 + 1 = 165 > 132. Impossible!
    · -- Step 10: Element counting argument.
      -- Step 10.1: For |G| = 132 = 2² × 3 × 11, Sylow-11 subgroups have order 11 and Sylow-3 have order 3.
      -- Step 10.2: Distinct Sylow p-subgroups of prime order p intersect trivially (since any subgroup
      -- of a group of prime order is either trivial or the whole group).
      -- Step 10.3: Sylow-11 and Sylow-3 subgroups have coprime orders (11 and 3), so intersect trivially.
      -- Step 10.4: With n₁₁ = 12 Sylow-11 subgroups: 12 × (11 - 1) = 120 non-identity elements.
      -- Step 10.5: With n₃ = 22 Sylow-3 subgroups: 22 × (3 - 1) = 44 non-identity elements.
      -- Step 10.6: Total distinct elements: 120 + 44 + 1 (identity) = 165 > 132 = |G|.
      -- Step 10.7: This contradicts |G| = 132.

      -- Step 11: Establish the Sylow subgroup cardinalities.
      -- Step 11.1: Each Sylow-11 subgroup has 11 elements.
      have hSylow11_card : ∀ S : Sylow 11 G, Nat.card S.toSubgroup = 11 := fun S => by
        have h := Sylow.card_eq_multiplicity (G := G) (p := 11) S
        have hFactor : Nat.factorization (Nat.card G) 11 = 1 := by
          rw [h_card_nat]
          -- 132 = 4 * 3 * 11 = 2² * 3 * 11, so 11¹ exactly divides 132
          native_decide
        rw [h, hFactor, pow_one]

      -- Step 11.2: Each Sylow-3 subgroup has 3 elements.
      have hSylow3_card : ∀ S : Sylow 3 G, Nat.card S.toSubgroup = 3 := fun S => by
        have h := Sylow.card_eq_multiplicity (G := G) (p := 3) S
        have hFactor : Nat.factorization (Nat.card G) 3 = 1 := by
          rw [h_card_nat]
          -- 132 = 4 * 3 * 11 = 2² * 3¹ * 11, so 3¹ exactly divides 132
          native_decide
        rw [h, hFactor, pow_one]

      -- Step 12: Define non-identity elements of a Sylow subgroup.
      -- Step 12.1: For a prime p, the non-identity elements of a Sylow-p subgroup S
      -- are those g ∈ S with g ≠ 1. For |S| = p prime, there are exactly p - 1 such elements.

      -- Step 12.2: Define the set of non-identity elements in Sylow-11 subgroups as a Finset.
      let sylowNonId11 (S : Sylow 11 G) : Finset G :=
        (S.toSubgroup : Set G).toFinset \ {1}

      -- Step 12.3: Define the set of non-identity elements in Sylow-3 subgroups as a Finset.
      let sylowNonId3 (S : Sylow 3 G) : Finset G :=
        (S.toSubgroup : Set G).toFinset \ {1}

      -- Step 13: Cardinality of non-identity elements in each Sylow subgroup.
      -- Step 13.1: Each Sylow-11 subgroup contributes 10 non-identity elements.
      have hCardNonId11 : ∀ S : Sylow 11 G, (sylowNonId11 S).card = 10 := fun S => by
        have hS_card := hSylow11_card S
        simp only [Nat.card_eq_fintype_card] at hS_card
        have h_inter : ({1} : Finset G) ∩ (S.toSubgroup : Set G).toFinset = {1} := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_singleton, Set.mem_toFinset, SetLike.mem_coe]
          constructor
          · intro ⟨hx, _⟩; exact hx
          · intro hx; exact ⟨hx, hx ▸ S.toSubgroup.one_mem⟩
        have h1 : ((S.toSubgroup : Set G).toFinset \ {1}).card
                = (S.toSubgroup : Set G).toFinset.card - ({1} ∩ (S.toSubgroup : Set G).toFinset).card :=
          Finset.card_sdiff
        have h2 : ({1} ∩ (S.toSubgroup : Set G).toFinset).card = 1 := by
          rw [h_inter]; exact Finset.card_singleton 1
        have h3 : (S.toSubgroup : Set G).toFinset.card = 11 := by
          simp only [Set.toFinset_card, SetLike.coe_sort_coe, hS_card]
        rw [h1, h2, h3]

      -- Step 13.2: Each Sylow-3 subgroup contributes 2 non-identity elements.
      have hCardNonId3 : ∀ S : Sylow 3 G, (sylowNonId3 S).card = 2 := fun S => by
        have hS_card := hSylow3_card S
        simp only [Nat.card_eq_fintype_card] at hS_card
        have h_inter : ({1} : Finset G) ∩ (S.toSubgroup : Set G).toFinset = {1} := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_singleton, Set.mem_toFinset, SetLike.mem_coe]
          constructor
          · intro ⟨hx, _⟩; exact hx
          · intro hx; exact ⟨hx, hx ▸ S.toSubgroup.one_mem⟩
        have h1 : ((S.toSubgroup : Set G).toFinset \ {1}).card
                = (S.toSubgroup : Set G).toFinset.card - ({1} ∩ (S.toSubgroup : Set G).toFinset).card :=
          Finset.card_sdiff
        have h2 : ({1} ∩ (S.toSubgroup : Set G).toFinset).card = 1 := by
          rw [h_inter]; exact Finset.card_singleton 1
        have h3 : (S.toSubgroup : Set G).toFinset.card = 3 := by
          simp only [Set.toFinset_card, SetLike.coe_sort_coe, hS_card]
        rw [h1, h2, h3]

      -- Step 14: Disjointness of non-identity elements between distinct Sylow subgroups.
      -- Step 14.1: Two distinct Sylow-11 subgroups share only identity.
      -- (Since each has prime order 11, any subgroup is either trivial or the whole group.
      -- If they share a non-identity element g, then ⟨g⟩ = S₁ = S₂, contradiction.)
      have hDisjoint11 : ∀ S₁ S₂ : Sylow 11 G, S₁ ≠ S₂ → Disjoint (sylowNonId11 S₁) (sylowNonId11 S₂) := by
        intro S₁ S₂ hne
        rw [Finset.disjoint_iff_ne]
        intro g hg1 h hg2
        unfold sylowNonId11 at hg1 hg2
        simp only [Finset.mem_sdiff, Set.mem_toFinset, SetLike.mem_coe, Finset.mem_singleton] at hg1 hg2
        obtain ⟨hgS1, hg_ne1⟩ := hg1
        obtain ⟨hgS2, _⟩ := hg2
        intro heq; subst heq
        -- Step 14.1.1: g is in both S₁ and S₂, and g ≠ 1.
        -- Step 14.1.2: Since |S₁| = 11 is prime and g ∈ S₁ with g ≠ 1, orderOf g = 11.
        have hS1_card := hSylow11_card S₁
        have hS2_card := hSylow11_card S₂
        simp only [Nat.card_eq_fintype_card] at hS1_card hS2_card
        have h_ord_dvd : orderOf g ∣ 11 := by
          have h1 : orderOf (⟨g, hgS1⟩ : S₁.toSubgroup) ∣ Fintype.card S₁.toSubgroup := orderOf_dvd_card
          have h2 : orderOf (⟨g, hgS1⟩ : S₁.toSubgroup) = orderOf g := (Subgroup.orderOf_coe _).symm
          rw [h2, hS1_card] at h1; exact h1
        have h_ord_eq : orderOf g = 11 :=
          (h_prime11.eq_one_or_self_of_dvd _ h_ord_dvd).resolve_left
            (fun h => hg_ne1 (orderOf_eq_one_iff.mp h))
        -- Step 14.1.3: ⟨g⟩ has order 11, so ⟨g⟩ = S₁ and ⟨g⟩ = S₂ (both have order 11).
        have h_zpowers_card : Nat.card (zpowers g) = 11 := by rw [Nat.card_zpowers, h_ord_eq]
        have h_le_S1 : zpowers g ≤ S₁.toSubgroup := Subgroup.zpowers_le_of_mem hgS1
        have h_eq_S1 : zpowers g = S₁.toSubgroup := by
          apply le_antisymm h_le_S1
          intro x hx
          by_contra h_not
          have h_strict : zpowers g < S₁.toSubgroup := lt_of_le_of_ne h_le_S1 (fun h => h_not (h ▸ hx))
          have h_card_lt : Nat.card (zpowers g) < Nat.card S₁.toSubgroup := by
            have h_ssubset : (zpowers g : Set G) ⊂ (S₁.toSubgroup : Set G) := h_strict
            have h_finite : (S₁.toSubgroup : Set G).Finite := Set.toFinite _
            exact h_finite.card_lt_card h_ssubset
          rw [h_zpowers_card, hSylow11_card S₁] at h_card_lt
          exact Nat.lt_irrefl 11 h_card_lt
        have h_le_S2 : zpowers g ≤ S₂.toSubgroup := Subgroup.zpowers_le_of_mem hgS2
        have h_eq_S2 : zpowers g = S₂.toSubgroup := by
          apply le_antisymm h_le_S2
          intro x hx
          by_contra h_not
          have h_strict : zpowers g < S₂.toSubgroup := lt_of_le_of_ne h_le_S2 (fun h => h_not (h ▸ hx))
          have h_card_lt : Nat.card (zpowers g) < Nat.card S₂.toSubgroup := by
            have h_ssubset : (zpowers g : Set G) ⊂ (S₂.toSubgroup : Set G) := h_strict
            have h_finite : (S₂.toSubgroup : Set G).Finite := Set.toFinite _
            exact h_finite.card_lt_card h_ssubset
          rw [h_zpowers_card, hSylow11_card S₂] at h_card_lt
          exact Nat.lt_irrefl 11 h_card_lt
        -- Step 14.1.4: S₁ = ⟨g⟩ = S₂, contradicting S₁ ≠ S₂.
        have : S₁.toSubgroup = S₂.toSubgroup := by rw [← h_eq_S1, h_eq_S2]
        exact hne (Sylow.ext this)

      -- Step 14.2: Two distinct Sylow-3 subgroups share only identity.
      have hDisjoint3 : ∀ S₁ S₂ : Sylow 3 G, S₁ ≠ S₂ → Disjoint (sylowNonId3 S₁) (sylowNonId3 S₂) := by
        intro S₁ S₂ hne
        rw [Finset.disjoint_iff_ne]
        intro g hg1 h hg2
        unfold sylowNonId3 at hg1 hg2
        simp only [Finset.mem_sdiff, Set.mem_toFinset, SetLike.mem_coe, Finset.mem_singleton] at hg1 hg2
        obtain ⟨hgS1, hg_ne1⟩ := hg1
        obtain ⟨hgS2, _⟩ := hg2
        intro heq; subst heq
        have hS1_card := hSylow3_card S₁
        have hS2_card := hSylow3_card S₂
        simp only [Nat.card_eq_fintype_card] at hS1_card hS2_card
        have h_ord_dvd : orderOf g ∣ 3 := by
          have h1 : orderOf (⟨g, hgS1⟩ : S₁.toSubgroup) ∣ Fintype.card S₁.toSubgroup := orderOf_dvd_card
          have h2 : orderOf (⟨g, hgS1⟩ : S₁.toSubgroup) = orderOf g := (Subgroup.orderOf_coe _).symm
          rw [h2, hS1_card] at h1; exact h1
        have h_ord_eq : orderOf g = 3 :=
          (h_prime3.eq_one_or_self_of_dvd _ h_ord_dvd).resolve_left
            (fun h => hg_ne1 (orderOf_eq_one_iff.mp h))
        have h_zpowers_card : Nat.card (zpowers g) = 3 := by rw [Nat.card_zpowers, h_ord_eq]
        have h_le_S1 : zpowers g ≤ S₁.toSubgroup := Subgroup.zpowers_le_of_mem hgS1
        have h_eq_S1 : zpowers g = S₁.toSubgroup := by
          apply le_antisymm h_le_S1
          intro x hx
          by_contra h_not
          have h_strict : zpowers g < S₁.toSubgroup := lt_of_le_of_ne h_le_S1 (fun h => h_not (h ▸ hx))
          have h_card_lt : Nat.card (zpowers g) < Nat.card S₁.toSubgroup := by
            have h_ssubset : (zpowers g : Set G) ⊂ (S₁.toSubgroup : Set G) := h_strict
            have h_finite : (S₁.toSubgroup : Set G).Finite := Set.toFinite _
            exact h_finite.card_lt_card h_ssubset
          rw [h_zpowers_card, hSylow3_card S₁] at h_card_lt
          exact Nat.lt_irrefl 3 h_card_lt
        have h_le_S2 : zpowers g ≤ S₂.toSubgroup := Subgroup.zpowers_le_of_mem hgS2
        have h_eq_S2 : zpowers g = S₂.toSubgroup := by
          apply le_antisymm h_le_S2
          intro x hx
          by_contra h_not
          have h_strict : zpowers g < S₂.toSubgroup := lt_of_le_of_ne h_le_S2 (fun h => h_not (h ▸ hx))
          have h_card_lt : Nat.card (zpowers g) < Nat.card S₂.toSubgroup := by
            have h_ssubset : (zpowers g : Set G) ⊂ (S₂.toSubgroup : Set G) := h_strict
            have h_finite : (S₂.toSubgroup : Set G).Finite := Set.toFinite _
            exact h_finite.card_lt_card h_ssubset
          rw [h_zpowers_card, hSylow3_card S₂] at h_card_lt
          exact Nat.lt_irrefl 3 h_card_lt
        have : S₁.toSubgroup = S₂.toSubgroup := by rw [← h_eq_S1, h_eq_S2]
        exact hne (Sylow.ext this)

      -- Step 14.3: Sylow-11 and Sylow-3 subgroups share only identity.
      -- (Since |S₁₁| = 11 and |S₃| = 3 are coprime, S₁₁ ∩ S₃ = {1}.)
      have hDisjoint11_3 : ∀ (S₁₁ : Sylow 11 G) (S₃ : Sylow 3 G),
          Disjoint (sylowNonId11 S₁₁) (sylowNonId3 S₃) := by
        intro S₁₁ S₃
        rw [Finset.disjoint_iff_ne]
        intro g hg11 h hg3
        dsimp only [sylowNonId11, sylowNonId3] at hg11 hg3
        simp only [Finset.mem_sdiff, Set.mem_toFinset, SetLike.mem_coe, Finset.mem_singleton] at hg11 hg3
        obtain ⟨hgS11, hg_ne1_11⟩ := hg11
        obtain ⟨hgS3, hg_ne1_3⟩ := hg3
        intro heq; subst heq
        -- Step 14.3.1: g is in both S₁₁ and S₃, and g ≠ 1.
        -- Step 14.3.2: orderOf g divides both 11 and 3.
        have hS11_card := hSylow11_card S₁₁
        have hS3_card := hSylow3_card S₃
        simp only [Nat.card_eq_fintype_card] at hS11_card hS3_card
        have h_ord_dvd_11 : orderOf g ∣ 11 := by
          have h1 : orderOf (⟨g, hgS11⟩ : S₁₁.toSubgroup) ∣ Fintype.card S₁₁.toSubgroup := orderOf_dvd_card
          have h2 : orderOf (⟨g, hgS11⟩ : S₁₁.toSubgroup) = orderOf g := (Subgroup.orderOf_coe _).symm
          rw [h2, hS11_card] at h1; exact h1
        have h_ord_dvd_3 : orderOf g ∣ 3 := by
          have h1 : orderOf (⟨g, hgS3⟩ : S₃.toSubgroup) ∣ Fintype.card S₃.toSubgroup := orderOf_dvd_card
          have h2 : orderOf (⟨g, hgS3⟩ : S₃.toSubgroup) = orderOf g := (Subgroup.orderOf_coe _).symm
          rw [h2, hS3_card] at h1; exact h1
        -- Step 14.3.3: gcd(11, 3) = 1, so orderOf g ∣ 1, so orderOf g = 1, so g = 1.
        have hcop : Nat.Coprime 11 3 := by decide
        have h_ord_dvd_1 : orderOf g ∣ 1 := by
          have h := Nat.dvd_gcd h_ord_dvd_11 h_ord_dvd_3
          rwa [hcop] at h
        have h_ord_eq_1 : orderOf g = 1 := Nat.eq_one_of_dvd_one h_ord_dvd_1
        have hg_eq_1 : g = 1 := orderOf_eq_one_iff.mp h_ord_eq_1
        exact hg_ne1_11 hg_eq_1

      -- Step 15: Define the union of all non-identity elements in Sylow subgroups.
      -- Step 15.1: All non-identity elements of Sylow-11 subgroups.
      let allNonId11 : Finset G := Finset.univ.biUnion sylowNonId11
      -- Step 15.2: All non-identity elements of Sylow-3 subgroups.
      let allNonId3 : Finset G := Finset.univ.biUnion sylowNonId3

      -- Step 16: Cardinality of the union of all Sylow-11 non-identity elements.
      -- Step 16.1: Since distinct Sylow-11 subgroups have disjoint non-identity elements,
      -- |allNonId11| = n₁₁ × (11 - 1) = 12 × 10 = 120.
      have hCardAllNonId11 : allNonId11.card = 12 * 10 := by
        have hbiUnion_card : allNonId11.card = (Finset.univ (α := Sylow 11 G)).card * 10 := by
          dsimp only [allNonId11]
          rw [Finset.card_biUnion]
          · simp only [hCardNonId11, Finset.sum_const, smul_eq_mul, Finset.card_univ]
          · intro S₁ _ S₂ _ hne; exact hDisjoint11 S₁ S₂ hne
        rw [hbiUnion_card]
        have hn11_fintype : Fintype.card (Sylow 11 G) = 12 := by
          rw [Fintype.card_eq_nat_card, ← hn11_def, hn11_12]
        rw [Finset.card_univ, hn11_fintype]

      -- Step 16.2: Since distinct Sylow-3 subgroups have disjoint non-identity elements,
      -- |allNonId3| = n₃ × (3 - 1) = 22 × 2 = 44.
      have hCardAllNonId3 : allNonId3.card = 22 * 2 := by
        have hbiUnion_card : allNonId3.card = (Finset.univ (α := Sylow 3 G)).card * 2 := by
          dsimp only [allNonId3]
          rw [Finset.card_biUnion]
          · simp only [hCardNonId3, Finset.sum_const, smul_eq_mul, Finset.card_univ]
          · intro S₁ _ S₂ _ hne; exact hDisjoint3 S₁ S₂ hne
        rw [hbiUnion_card]
        have hn3_fintype : Fintype.card (Sylow 3 G) = 22 := by
          rw [Fintype.card_eq_nat_card, ← hn3_def, hn3_22]
        rw [Finset.card_univ, hn3_fintype]

      -- Step 17: Sylow-11 and Sylow-3 non-identity elements are disjoint.
      have hDisjointAll : Disjoint allNonId11 allNonId3 := by
        rw [Finset.disjoint_iff_ne]
        intro g hg11 h hg3
        dsimp only [allNonId11, allNonId3] at hg11 hg3
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hg11 hg3
        obtain ⟨S₁₁, hgS11⟩ := hg11
        obtain ⟨S₃, hgS3⟩ := hg3
        have hDisj := hDisjoint11_3 S₁₁ S₃
        rw [Finset.disjoint_iff_ne] at hDisj
        exact hDisj g hgS11 h hgS3

      -- Step 18: 1 is not in allNonId11 or allNonId3.
      have h1_not_in_11 : (1 : G) ∉ allNonId11 := by
        dsimp only [allNonId11, sylowNonId11]
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists,
                   Finset.mem_sdiff, Set.mem_toFinset, SetLike.mem_coe, Finset.mem_singleton,
                   not_and, not_not]
        intro S _; trivial
      have h1_not_in_3 : (1 : G) ∉ allNonId3 := by
        dsimp only [allNonId3, sylowNonId3]
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists,
                   Finset.mem_sdiff, Set.mem_toFinset, SetLike.mem_coe, Finset.mem_singleton,
                   not_and, not_not]
        intro S _; trivial

      -- Step 19: Cardinality of the combined set.
      -- |{1} ∪ allNonId11 ∪ allNonId3| = 1 + 120 + 44 = 165.
      let combinedSet : Finset G := insert 1 (allNonId11 ∪ allNonId3)
      have h1_not_in_union : (1 : G) ∉ allNonId11 ∪ allNonId3 := by
        simp only [Finset.mem_union, not_or]
        exact ⟨h1_not_in_11, h1_not_in_3⟩

      have hCardCombined : combinedSet.card = 165 := by
        have h1 : combinedSet.card = (allNonId11 ∪ allNonId3).card + 1 := by
          unfold combinedSet
          exact Finset.card_insert_of_notMem h1_not_in_union
        have h2 : (allNonId11 ∪ allNonId3).card = allNonId11.card + allNonId3.card :=
          Finset.card_union_of_disjoint hDisjointAll
        rw [h1, h2, hCardAllNonId11, hCardAllNonId3]

      -- Step 20: The combined set is a subset of G, so its cardinality ≤ |G| = 132.
      have hCombined_le_G : combinedSet.card ≤ Fintype.card G := Finset.card_le_univ combinedSet

      -- Step 21: But 165 > 132, contradiction!
      rw [hCardCombined, hG] at hCombined_le_G
      omega
