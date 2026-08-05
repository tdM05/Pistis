import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that if $|G|=462$ then $G$ is not simple.
-/

/-Informal Proof

Let $G$ be a group of order $462=11 \cdot 42$. Note that 11 is a prime not dividing 42 . Let $P \in$ $S y l_{11}(G)$. [We know $P$ exists since $S y l_{11}(G) \neq \emptyset$]. Note that $|P|=11^1=11$ by definition. 

The number of Sylow 11-subgroups of $G$ is of the form $1+k \cdot 11$, i.e., $n_{11} \equiv 1$ (mod 11) and $n_{11}$ divides 42 . The only such number that divides 42 and equals 1 (mod 11) is 1 so $n_{11}=1$. Hence $P$ is the unique Sylow 11-subgroup.

Since $P$ is the unique Sylow Il-subgroup, this implies that $P$ is normal in $G$.
-/

theorem Dummit_Foote_exercise_4_5_23 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 462) : ¬ IsSimpleGroup G := by
  classical
  intro hSimple
  haveI : IsSimpleGroup G := hSimple
  -- Step 1: Collect arithmetic data about |G| and fix the Sylow-11 subgroup count.
  -- Step 1.1: Translate the hypothesis |G| = 462 into the Nat.card language used by Sylow theory.
  have h_card_nat : Nat.card G = 462 := by simpa [Nat.card_eq_fintype_card] using hG
  -- Step 1.2: Record the prime, divisibility, and non-divisibility facts about 11 inside |G|.
  have h_factor : Nat.card G = 11 * 42 :=
    h_card_nat.trans (by decide : 462 = 11 * 42)
  have h_prime11 : Nat.Prime 11 := by decide
  haveI : Fact (Nat.Prime 11) := ⟨h_prime11⟩
  have h_dvd_11 : 11 ∣ Nat.card G := by
    rcases (by decide : 11 ∣ 462) with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    exact h_card_nat.trans ht
  have h_not_dvd_sq : ¬ 11 ^ 2 ∣ Nat.card G := by
    intro hcontr
    rcases hcontr with ⟨t, ht⟩
    have hrewrite : 462 = 11 ^ 2 * t := h_card_nat.symm.trans ht
    have : 11 ^ 2 ∣ 462 := ⟨t, hrewrite⟩
    exact (by decide : ¬ 11 ^ 2 ∣ 462) this
  -- Step 1.3: Choose a Sylow-11 subgroup and denote by n₁₁ the number of such subgroups.
  obtain ⟨P⟩ := Sylow.nonempty (G := G) (p := 11)
  set n11 : ℕ := Nat.card (Sylow 11 G) with hn11
  -- Step 2: Force the number n₁₁ to equal 1 via the Sylow divisibility and congruence constraints.
  -- Step 2.1: Combine the counting lemmas to obtain divisibility information.
  have hn_dvd_card : n11 ∣ Nat.card G := by
    have h_dvd_index : n11 ∣ P.index := by
      simpa [n11] using (Sylow.card_dvd_index (p := 11) (G := G) P)
    exact Nat.dvd_trans h_dvd_index P.1.index_dvd_card
  have h_mod : n11 ≡ 1 [MOD 11] := card_sylow_modEq_one (p := 11) (G := G)
  have h_coprime : Nat.Coprime n11 11 := by
    have h_not_dvd : ¬ 11 ∣ n11 := by
      simpa [n11] using (not_dvd_card_sylow (p := 11) (G := G))
    have h' : Nat.Coprime 11 n11 := (h_prime11.coprime_iff_not_dvd).2 h_not_dvd
    simpa [Nat.coprime_comm] using h'
  have hn_dvd_42 : n11 ∣ 42 := by
    rcases hn_dvd_card with ⟨t, ht⟩
    have h_aux : n11 ∣ 11 * 42 := ⟨t, h_factor.symm.trans ht⟩
    exact h_coprime.dvd_of_dvd_mul_left h_aux
  -- Step 2.2: Introduce the complementary factor m with 42 = n₁₁ · m and analyze its congruence.
  obtain ⟨m, hm⟩ := hn_dvd_42
  have h_mul_mod : n11 * m ≡ m [MOD 11] := by
    simpa [one_mul] using h_mod.mul_right m
  have h_prod_mod : n11 * m ≡ 42 [MOD 11] := by
    simp [Nat.ModEq, hm]
  have hm_modEq : m ≡ 42 [MOD 11] := h_mul_mod.symm.trans h_prod_mod
  have hm_dvd : m ∣ 42 := by
    refine ⟨n11, ?_⟩
    simpa [Nat.mul_comm] using hm
  have hm_mem : m ∈ Nat.divisors 42 :=
    (Nat.mem_divisors).2 ⟨hm_dvd, by decide⟩
  -- Step 2.3: Enumerate the divisors of 42 and keep only those compatible with the mod-11 condition.
  have h_divisors :
      Nat.divisors 42 =
        ({1, 2, 3, 6, 7, 14, 21, 42} : Finset ℕ) := by decide
  have hm_cases :
      m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6 ∨ m = 7 ∨ m = 14 ∨ m = 21 ∨ m = 42 := by
    have : m ∈ ({1, 2, 3, 6, 7, 14, 21, 42} : Finset ℕ) := by
      simpa [h_divisors] using hm_mem
    simpa [Finset.mem_insert, Finset.mem_singleton] using this
  have hm_eq_42 : m = 42 := by
    rcases hm_cases with hm_val | hm_val | hm_val | hm_val | hm_val | hm_val | hm_val | hm_val
    · have : False := by simp [Nat.ModEq, hm_val] at hm_modEq
      exact this.elim
    · have : False := by simp [Nat.ModEq, hm_val] at hm_modEq
      exact this.elim
    · have : False := by simp [Nat.ModEq, hm_val] at hm_modEq
      exact this.elim
    · have : False := by simp [Nat.ModEq, hm_val] at hm_modEq
      exact this.elim
    · have : False := by simp [Nat.ModEq, hm_val] at hm_modEq
      exact this.elim
    · have : False := by simp [Nat.ModEq, hm_val] at hm_modEq
      exact this.elim
    · have : False := by simp [Nat.ModEq, hm_val] at hm_modEq
      exact this.elim
    · exact hm_val
  -- Step 2.4: Deduce that n₁₁ = 1 from 42 = n₁₁ · 42 and translate this into uniqueness information.
  have h_eq : n11 * 42 = 1 * 42 := by
    simpa [hm_eq_42, Nat.mul_comm, one_mul] using hm.symm
  have hn_eq_one : n11 = 1 :=
    Nat.mul_right_cancel (by decide : 0 < 42) h_eq
  have h_card_one : Nat.card (Sylow 11 G) = 1 := by simpa [n11] using hn_eq_one
  have h_subsingleton : Subsingleton (Sylow 11 G) :=
    (Nat.card_eq_one_iff_unique).1 h_card_one |>.1
  -- Step 3: Turn the unique Sylow-11 subgroup into a proper nontrivial normal subgroup.
  -- Step 3.1: Promote the subsingleton information to normality of the chosen Sylow subgroup.
  letI : Subsingleton (Sylow 11 G) := h_subsingleton
  have hP_normal : P.Normal := Sylow.normal_of_subsingleton (p := 11) (G := G) P
  -- Step 3.2: Compute the exact order of P to show it is nontrivial and not all of G.
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hk_ne_zero : k ≠ 0 := by
    intro hk0
    have h_dvd_cardP : 11 ∣ Nat.card ↥(P : Subgroup G) :=
      P.dvd_card_of_dvd_card h_dvd_11
    rcases h_dvd_cardP with ⟨t, htP⟩
    have h_card_one : Nat.card ↥(P : Subgroup G) = 1 := by
      simpa [hk0] using hk
    have hrewrite : 1 = 11 * t := h_card_one ▸ htP
    have h_div_one : 11 ∣ 1 := ⟨t, hrewrite⟩
    exact h_prime11.ne_one (Nat.dvd_one.mp h_div_one)
  have hk_ge_one : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk_ne_zero)
  have h_card_divides : Nat.card ↥(P : Subgroup G) ∣ Nat.card G :=
    (P : Subgroup G).card_subgroup_dvd_card
  have hk_le_one : k ≤ 1 := by
    by_contra hk_gt
    have hk_ge_two : 2 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_not_ge hk_gt)
    have h_pow_dvd : 11 ^ 2 ∣ 11 ^ k := pow_dvd_pow 11 hk_ge_two
    have h_cardPow : 11 ^ k ∣ Nat.card G := by
      rcases h_card_divides with ⟨s, hs⟩
      have h_eq := hs
      rw [hk] at h_eq
      exact ⟨s, by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h_eq⟩
    have : 11 ^ 2 ∣ Nat.card G := dvd_trans h_pow_dvd h_cardPow
    exact h_not_dvd_sq this
  have hk_one : k = 1 := le_antisymm hk_le_one hk_ge_one
  have h_card_P : Nat.card ↥(P : Subgroup G) = 11 := by
    simpa [hk_one, pow_one] using hk
  have hP_ne_bot : (P : Subgroup G) ≠ ⊥ :=
    P.ne_bot_of_dvd_card h_dvd_11
  have hP_ne_top : (P : Subgroup G) ≠ ⊤ := by
    intro htop
    have h_card_eq : Nat.card ↥(P : Subgroup G) = Nat.card G := by
      simp [htop]
    have h_eq_num : 11 = 462 := by
      calc
        11 = Nat.card ↥(P : Subgroup G) := h_card_P.symm
        _ = Nat.card G := h_card_eq
        _ = 462 := h_card_nat
    exact (by decide : 11 ≠ 462) h_eq_num
  -- Step 3.3: Invoke simplicity to obtain the final contradiction from the proper normal subgroup.
  have h_options := hSimple.eq_bot_or_eq_top_of_normal (P : Subgroup G) hP_normal
  cases h_options with
  | inl hbot => exact hP_ne_bot hbot
  | inr htop => exact hP_ne_top htop
