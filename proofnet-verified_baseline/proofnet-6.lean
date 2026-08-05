import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators



/-Informal Statement

Prove that no group of order $p^2 q$, where $p$ and $q$ are prime, is simple.
-/

/-Informal Proof

We may as well assume $p<q$. The number of Sylow $q$-subgroups is $1 \bmod q$ and divides $p^2$. So it is $1, p$, or $p^2$. We win if it's 1 and it can't be $p$, so suppose it's $p^2$. But now $q \mid p^2-1$, so $q \mid p+1$ or $q \mid p-1$.
Thus $p=2$ and $q=3$. But we know no group of order 36 is simple.
-/

theorem Artin_exercise_6_4_3 {G : Type*} [Group G] [Fintype G] {p q : ℕ}
  (hp : Prime p) (hq : Prime q) (hG : card G = p^2 * q) :
  IsSimpleGroup G → False := by
  classical
  -- Step 1: Introduce the simplicity hypothesis and set up instances
  -- Step 1.1: Get the simplicity hypothesis as an instance
  intro hSimple
  haveI := hSimple
  -- Step 1.2: Convert algebraic Prime to Nat.Prime for use with Sylow theorems
  have hp_nat : Nat.Prime p := hp.nat_prime
  have hq_nat : Nat.Prime q := hq.nat_prime
  haveI hpFact : Fact (Nat.Prime p) := ⟨hp_nat⟩
  haveI hqFact : Fact (Nat.Prime q) := ⟨hq_nat⟩

  -- Step 2: Handle the special case p = q first
  -- When p = q, |G| = p^3, and G is a p-group
  -- A p-group has nontrivial center, and a simple group with nontrivial center
  -- must be abelian of prime order. But |G| = p^3 is not prime, contradiction.
  by_cases hpq : p = q
  · -- Step 2.1: Case p = q
    subst hpq
    -- Step 2.1.1: |G| = p^3
    have hG_eq_p3 : card G = p^3 := by
      calc card G = p^2 * p := hG
        _ = p^3 := by ring
    -- Step 2.1.2: G is a p-group
    have hG_pgroup : IsPGroup p G := by
      rw [IsPGroup.iff_card]
      use 3
      simp only [Nat.card_eq_fintype_card]
      exact hG_eq_p3
    -- Step 2.1.3: The center of a nontrivial p-group is nontrivial
    have hG_gt_1 : 1 < card G := by
      rw [hG_eq_p3]
      have hp_ge_2 : 2 ≤ p := hp_nat.two_le
      calc p^3 = p * p * p := by ring
        _ ≥ 2 * 2 * 2 := by nlinarith
        _ = 8 := by norm_num
        _ > 1 := by norm_num
    have hG_nontrivial : Nontrivial G := by
      rw [← Fintype.one_lt_card_iff_nontrivial]
      exact hG_gt_1
    haveI := hG_nontrivial
    have hCenter_nontrivial : Nontrivial (Subgroup.center G) := hG_pgroup.center_nontrivial
    -- Step 2.1.4: The center is a nontrivial normal subgroup
    have hCenter_normal : (Subgroup.center G).Normal := inferInstance
    -- Step 2.1.5: By simplicity, center = ⊥ or center = ⊤
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) hCenter_normal with hBot | hTop
    · -- Step 2.1.6: center = ⊥ contradicts center being nontrivial
      have hCenter_trivial : ¬Nontrivial (Subgroup.center G) := by
        rw [hBot]
        exact not_nontrivial (⊥ : Subgroup G)
      exact hCenter_trivial hCenter_nontrivial
    · -- Step 2.1.7: center = ⊤ means G is abelian
      -- We need to show a contradiction. Since center = G, any proper subgroup H is
      -- also normal, so G being simple forces every proper normal subgroup to be ⊥.
      -- This means G has no proper nontrivial subgroups.
      -- But |G| = p^3 > p, so by Lagrange any element g with 1 < order(g) < p^3
      -- generates a proper nontrivial subgroup.

      -- The key insight: if |G| = p^3 is not prime, then G has a subgroup of order p
      -- (any element of order p generates such a subgroup, and such elements exist
      -- because p | |G| by Cauchy's theorem)

      -- Actually, let's use a simpler argument:
      -- We already know the center is nontrivial. If center = G, then G is abelian.
      -- For abelian simple groups, the only normal subgroups are ⊥ and G.
      -- But an abelian group G of order p^3 has a subgroup of order p (by Cauchy).
      -- This subgroup is normal (G abelian), nontrivial, and proper (order p < p^3).
      -- Contradiction.

      have hG_abelian : CommGroup G := Group.commGroupOfCenterEqTop hTop
      -- By Cauchy's theorem, since p | |G|, there exists an element of order p
      have hp_dvd : p ∣ card G := by
        rw [hG_eq_p3]
        exact dvd_pow_self p (by norm_num : 3 ≠ 0)
      -- Get an element of order p
      obtain ⟨g, hg_ord⟩ := exists_prime_orderOf_dvd_card p hp_dvd
      -- The subgroup ⟨g⟩ has order p
      have hZpg_card : Nat.card (Subgroup.zpowers g) = p := by
        have := Nat.card_zpowers (a := g)
        rw [hg_ord] at this
        exact this
      -- This subgroup is normal (G is abelian, center = G)
      -- Since center = ⊤, the group is commutative and all subgroups are normal
      have hZpg_normal : (Subgroup.zpowers g).Normal := by
        -- When center = ⊤, every element commutes with every other element
        -- So conjugation is trivial: x * n * x⁻¹ = n for all x, n
        constructor
        intro n hn x
        -- Need to show x * n * x⁻¹ ∈ Subgroup.zpowers g
        -- Since n is in the center (center = ⊤), n commutes with x
        have hn_center : n ∈ Subgroup.center G := by rw [hTop]; trivial
        have hcomm : x * n = n * x := Subgroup.mem_center_iff.mp hn_center x
        -- So x * n * x⁻¹ = n
        convert hn using 1
        -- Goal: x * n * x⁻¹ = n
        -- From hcomm : x * n = n * x
        conv_lhs => rw [hcomm]
        simp [mul_assoc]
      -- By simplicity, ⟨g⟩ = ⊥ or ⟨g⟩ = ⊤
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers g) hZpg_normal with hBot | hZpg_Top
      · -- Case ⟨g⟩ = ⊥: then |⟨g⟩| = 1, but |⟨g⟩| = p ≥ 2
        have hCard_bot : Nat.card (⊥ : Subgroup G) = 1 := Subgroup.card_bot
        have hp_eq_1 : p = 1 := by
          calc p = Nat.card (Subgroup.zpowers g) := hZpg_card.symm
            _ = Nat.card (⊥ : Subgroup G) := by rw [hBot]
            _ = 1 := hCard_bot
        have hp_ge_2 : p ≥ 2 := hp_nat.two_le
        omega
      · -- Case ⟨g⟩ = ⊤: then |⟨g⟩| = |G|, but |⟨g⟩| = p and |G| = p^3
        have hCard_top : Nat.card (⊤ : Subgroup G) = Nat.card G := Subgroup.card_top
        have hp_eq_p3 : p = card G := by
          calc p = Nat.card (Subgroup.zpowers g) := hZpg_card.symm
            _ = Nat.card (⊤ : Subgroup G) := by rw [hZpg_Top]
            _ = Nat.card G := hCard_top
            _ = card G := Nat.card_eq_fintype_card
        rw [hG_eq_p3] at hp_eq_p3
        have hp_ge_2 : p ≥ 2 := hp_nat.two_le
        -- p = p^3 implies p^2 = 1, but p ≥ 2 means p^2 ≥ 4
        have hp2_eq_1 : p^2 = 1 := by nlinarith
        have hp2_ge_4 : p^2 ≥ 4 := by nlinarith
        omega

  -- Step 3: Now handle the case p ≠ q
  -- Fix Sylow p-subgroup P and Sylow q-subgroup Q
  let P : Sylow p G := Classical.choice (inferInstance : Nonempty (Sylow p G))
  let Q : Sylow q G := Classical.choice (inferInstance : Nonempty (Sylow q G))

  -- Step 4: Compute the cardinality of P (Sylow p-subgroup has order p^2)
  have hCardP : Fintype.card P = p^2 := by
    -- Step 4.1: Use the Sylow multiplicity formula
    have h := Sylow.card_eq_multiplicity (G := G) (p := p) P
    have h' : Fintype.card P = p ^ Nat.factorization (Fintype.card G) p := by
      simpa [Nat.card_eq_fintype_card] using h
    -- Step 4.2: Compute the factorization of p^2 * q at p (where p ≠ q)
    have hFactor : Nat.factorization (Fintype.card G) p = 2 := by
      rw [hG]
      simp only [Nat.factorization_mul (pow_ne_zero 2 hp_nat.ne_zero) hq_nat.ne_zero]
      simp only [Nat.factorization_pow, Nat.Prime.factorization hp_nat]
      simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, if_true, smul_eq_mul, mul_one]
      simp only [Nat.Prime.factorization hq_nat, Finsupp.single_apply, if_neg (Ne.symm hpq), add_zero]
    rw [h', hFactor]

  -- Step 5: Compute the cardinality of Q (Sylow q-subgroup has order q)
  have hCardQ : Fintype.card Q = q := by
    -- Step 5.1: Use the Sylow multiplicity formula
    have h := Sylow.card_eq_multiplicity (G := G) (p := q) Q
    have h' : Fintype.card Q = q ^ Nat.factorization (Fintype.card G) q := by
      simpa [Nat.card_eq_fintype_card] using h
    -- Step 5.2: Compute the factorization of p^2 * q at q (where p ≠ q)
    have hFactor : Nat.factorization (Fintype.card G) q = 1 := by
      rw [hG]
      simp only [Nat.factorization_mul (pow_ne_zero 2 hp_nat.ne_zero) hq_nat.ne_zero]
      simp only [Nat.factorization_pow, Nat.Prime.factorization hp_nat, Nat.Prime.factorization hq_nat]
      simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
      simp only [if_neg hpq, if_true]
      norm_num
    rw [h', hFactor, pow_one]

  -- Step 6: Compute the index of P in G: [G : P] = q
  have hIndexP : P.index = q := by
    -- Step 6.1: Use index_mul_card: index * |P| = |G|
    have hMul : P.index * Fintype.card P = Fintype.card G := by
      have h := (P : Subgroup G).index_mul_card
      simpa [Nat.card_eq_fintype_card] using h
    -- Step 6.2: Substitute known values and solve
    have hEq : P.index * p^2 = p^2 * q := by
      simp only [hCardP, hG] at hMul
      exact hMul
    have hp2_pos : 0 < p^2 := pow_pos hp_nat.pos 2
    exact Nat.eq_of_mul_eq_mul_right hp2_pos (hEq.trans (mul_comm (p^2) q))

  -- Step 7: Compute the index of Q in G: [G : Q] = p^2
  have hIndexQ : Q.index = p^2 := by
    -- Step 7.1: Use index_mul_card: index * |Q| = |G|
    have hMul : Q.index * Fintype.card Q = Fintype.card G := by
      have h := (Q : Subgroup G).index_mul_card
      simpa [Nat.card_eq_fintype_card] using h
    -- Step 7.2: Substitute known values and solve
    have hEq : Q.index * q = p^2 * q := by
      simp only [hCardQ, hG] at hMul
      exact hMul
    have hq_pos : 0 < q := hq_nat.pos
    exact Nat.eq_of_mul_eq_mul_right hq_pos hEq

  -- Step 8: The number of Sylow q-subgroups divides the index [G : Q] = p^2
  -- and is congruent to 1 mod q
  have hNumQ_dvd : Nat.card (Sylow q G) ∣ p^2 := by
    have h := Sylow.card_dvd_index Q
    simp only [hIndexQ] at h
    exact h

  have hNumQ_mod : Nat.card (Sylow q G) ≡ 1 [MOD q] := card_sylow_modEq_one q G

  -- Step 9: The number of Sylow p-subgroups divides the index [G : P] = q
  -- and is congruent to 1 mod p
  have hNumP_dvd : Nat.card (Sylow p G) ∣ q := by
    have h := Sylow.card_dvd_index P
    simp only [hIndexP] at h
    exact h

  have hNumP_mod : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G

  -- Step 10: Handle the case where P is normal (n_p = 1)
  have hP_normal_case : Nat.card (Sylow p G) = 1 → False := by
    intro hOne
    -- Step 10.1: If there's exactly one Sylow p-subgroup, it's normal
    have hSubsingleton : Subsingleton (Sylow p G) := by
      rw [subsingleton_iff_forall_eq P]
      intro Q'
      have hFinite : Finite (Sylow p G) := inferInstance
      have hCard := hOne
      have : Fintype (Sylow p G) := Fintype.ofFinite _
      have hUnique : ∀ x y : Sylow p G, x = y := by
        intro x y
        have hcard_le : Fintype.card (Sylow p G) ≤ 1 := by
          simp only [Nat.card_eq_fintype_card] at hCard
          omega
        have := Fintype.card_le_one_iff.mp hcard_le
        exact this x y
      exact hUnique Q' P
    haveI := hSubsingleton
    have hNormal : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
    -- Step 10.2: By simplicity, P is either ⊥ or ⊤
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup G) hNormal with hBot | hTop
    · -- Step 10.3: Case P = ⊥: then |P| = 1, but we showed |P| = p^2 ≥ 4
      have hCardPOne : Nat.card (P : Subgroup G) = 1 := by
        rw [hBot]
        simp
      have hp_ge_2 : p ≥ 2 := hp_nat.two_le
      have hp2_gt_one : p^2 > 1 := by
        calc p^2 = p * p := by ring
          _ ≥ 2 * 2 := Nat.mul_le_mul hp_ge_2 hp_ge_2
          _ = 4 := by norm_num
          _ > 1 := by norm_num
      have hCardP_eq : Nat.card (P : Subgroup G) = p^2 := by
        simp only [Nat.card_eq_fintype_card]
        exact hCardP
      omega
    · -- Step 10.4: Case P = ⊤: then [G : P] = 1, but we showed [G : P] = q ≥ 2
      have hIndexTop : (⊤ : Subgroup G).index = 1 := Subgroup.index_top
      have hPTop : (P : Subgroup G) = ⊤ := hTop
      have hIndexPOne : P.index = 1 := by
        calc P.index = (P : Subgroup G).index := rfl
          _ = (⊤ : Subgroup G).index := by rw [hPTop]
          _ = 1 := hIndexTop
      have hq_ge_2 : q ≥ 2 := hq_nat.two_le
      omega

  -- Step 11: Handle the case where Q is normal (n_q = 1)
  have hQ_normal_case : Nat.card (Sylow q G) = 1 → False := by
    intro hOne
    -- Step 11.1: If there's exactly one Sylow q-subgroup, it's normal
    have hSubsingleton : Subsingleton (Sylow q G) := by
      rw [subsingleton_iff_forall_eq Q]
      intro Q'
      have hFinite : Finite (Sylow q G) := inferInstance
      have hCard := hOne
      have : Fintype (Sylow q G) := Fintype.ofFinite _
      have hUnique : ∀ x y : Sylow q G, x = y := by
        intro x y
        have hcard_le : Fintype.card (Sylow q G) ≤ 1 := by
          simp only [Nat.card_eq_fintype_card] at hCard
          omega
        have := Fintype.card_le_one_iff.mp hcard_le
        exact this x y
      exact hUnique Q' Q
    haveI := hSubsingleton
    have hNormal : (Q : Subgroup G).Normal := Sylow.normal_of_subsingleton Q
    -- Step 11.2: By simplicity, Q is either ⊥ or ⊤
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Q : Subgroup G) hNormal with hBot | hTop
    · -- Step 11.3: Case Q = ⊥: then |Q| = 1, but we showed |Q| = q ≥ 2
      have hCardQOne : Nat.card (Q : Subgroup G) = 1 := by
        rw [hBot]
        simp
      have hq_ge_2 : q ≥ 2 := hq_nat.two_le
      have hCardQ_eq : Nat.card (Q : Subgroup G) = q := by
        simp only [Nat.card_eq_fintype_card]
        exact hCardQ
      omega
    · -- Step 11.4: Case Q = ⊤: then [G : Q] = 1, but we showed [G : Q] = p^2 ≥ 4
      have hIndexTop : (⊤ : Subgroup G).index = 1 := Subgroup.index_top
      have hQTop : (Q : Subgroup G) = ⊤ := hTop
      have hIndexQOne : Q.index = 1 := by
        calc Q.index = (Q : Subgroup G).index := rfl
          _ = (⊤ : Subgroup G).index := by rw [hQTop]
          _ = 1 := hIndexTop
      have hp_ge_2 : p ≥ 2 := hp_nat.two_le
      have hp2_gt_one : p^2 > 1 := by
        calc p^2 = p * p := by ring
          _ ≥ 2 * 2 := Nat.mul_le_mul hp_ge_2 hp_ge_2
          _ = 4 := by norm_num
          _ > 1 := by norm_num
      omega

  -- Step 12: n_p divides q (prime), so n_p = 1 or n_p = q
  have hNumP_options : Nat.card (Sylow p G) = 1 ∨ Nat.card (Sylow p G) = q := by
    rcases Nat.Prime.eq_one_or_self_of_dvd hq_nat _ hNumP_dvd with h1 | hq'
    · left; exact h1
    · right; exact hq'

  -- Step 13: n_q divides p^2, so n_q ∈ {1, p, p^2}
  have hNumQ_options : Nat.card (Sylow q G) = 1 ∨ Nat.card (Sylow q G) = p ∨ Nat.card (Sylow q G) = p^2 := by
    have hp2_divs : ∀ d : ℕ, d ∣ p^2 → d = 1 ∨ d = p ∨ d = p^2 := by
      intro d hd
      rcases (Nat.dvd_prime_pow hp_nat).mp hd with ⟨k, hk_le, hk_eq⟩
      interval_cases k
      · left; simp at hk_eq; exact hk_eq
      · right; left; simp at hk_eq; exact hk_eq
      · right; right; exact hk_eq
    exact hp2_divs _ hNumQ_dvd

  -- Step 14: Analyze all cases
  rcases hNumP_options with hNumP_1 | hNumP_q
  · -- Case n_p = 1: contradiction with simplicity
    exact hP_normal_case hNumP_1
  · -- Case n_p = q
    -- Step 14.1: From n_p = q and n_p ≡ 1 (mod p), we get q ≡ 1 (mod p)
    have hq_mod_p : q ≡ 1 [MOD p] := by
      have h := hNumP_mod
      simp only [hNumP_q] at h
      exact h

    -- Step 14.2: q ≡ 1 (mod p) means p | q - 1, so q - 1 ≥ p (if q > 1), hence q > p
    have hq_gt_p : q > p := by
      have hq_ge_2 : q ≥ 2 := hq_nat.two_le
      have h1_le_q : 1 ≤ q := by omega
      have h : p ∣ q - 1 := (Nat.modEq_iff_dvd' h1_le_q).mp hq_mod_p.symm
      by_cases hqm1_zero : q - 1 = 0
      · omega
      · have hp_le : p ≤ q - 1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hqm1_zero) h
        omega

    -- Step 14.3: Now analyze n_q
    rcases hNumQ_options with hNumQ_1 | hNumQ_p | hNumQ_p2
    · -- Case n_q = 1: contradiction with simplicity
      exact hQ_normal_case hNumQ_1
    · -- Case n_q = p: then p ≡ 1 (mod q), so q | p - 1
      -- Step 14.3.1: p ≡ 1 (mod q)
      have hp_mod_q : p ≡ 1 [MOD q] := by
        have h := hNumQ_mod
        simp only [hNumQ_p] at h
        exact h
      -- Step 14.3.2: This means q | p - 1
      have hp_ge_2 : p ≥ 2 := hp_nat.two_le
      have h1_le_p : 1 ≤ p := by omega
      have hq_dvd_pminus1 : q ∣ p - 1 := (Nat.modEq_iff_dvd' h1_le_p).mp hp_mod_q.symm
      -- Step 14.3.3: But q > p, so p - 1 < q
      by_cases hpm1_zero : p - 1 = 0
      · omega
      · have hq_le : q ≤ p - 1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hpm1_zero) hq_dvd_pminus1
        omega
    · -- Case n_q = p^2: then p^2 ≡ 1 (mod q), so q | p^2 - 1 = (p-1)(p+1)
      -- Step 14.3.4: p^2 ≡ 1 (mod q)
      have hp2_mod_q : p^2 ≡ 1 [MOD q] := by
        have h := hNumQ_mod
        simp only [hNumQ_p2] at h
        exact h
      -- Step 14.3.5: This means q | p^2 - 1
      have hp_ge_2 : p ≥ 2 := hp_nat.two_le
      have h1_le_p2 : 1 ≤ p^2 := by nlinarith
      have hq_dvd_p2m1 : q ∣ p^2 - 1 := (Nat.modEq_iff_dvd' h1_le_p2).mp hp2_mod_q.symm
      -- Step 14.3.6: p^2 - 1 = (p - 1) * (p + 1) for p ≥ 1
      have hp2_factor : p^2 - 1 = (p - 1) * (p + 1) := by
        -- p^2 - 1^2 = (p + 1)(p - 1) = (p - 1)(p + 1)
        have h : p^2 - 1^2 = (p + 1) * (p - 1) := Nat.sq_sub_sq p 1
        simp only [one_pow] at h
        rw [mul_comm] at h
        exact h
      -- Step 14.3.7: Since q is prime and q | (p-1)(p+1), either q | p-1 or q | p+1
      rw [hp2_factor] at hq_dvd_p2m1
      have hq_dvd_or : q ∣ p - 1 ∨ q ∣ p + 1 := (Nat.Prime.dvd_mul hq_nat).mp hq_dvd_p2m1
      rcases hq_dvd_or with h_pm1 | h_pp1
      · -- Step 14.3.8: q | p - 1 case: same contradiction as before
        by_cases hpm1_zero : p - 1 = 0
        · omega
        · have hq_le : q ≤ p - 1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hpm1_zero) h_pm1
          omega
      · -- Step 14.3.9: q | p + 1 case
        -- Since q > p, we need p + 1 ≥ q for q | p + 1 to hold
        -- Combined with q > p, this gives q = p + 1
        have hq_le : q ≤ p + 1 := Nat.le_of_dvd (by omega) h_pp1
        have hq_eq : q = p + 1 := by omega

        -- Step 14.3.10: The only consecutive primes are 2 and 3
        have hp_eq_2 : p = 2 := by
          by_contra hp_ne_2
          have hp_gt_2 : p > 2 := by omega
          -- p > 2 and prime means p is odd
          have hp_odd : Odd p := hp_nat.odd_of_ne_two (by omega)
          -- Then q = p + 1 is even
          have hq_even : Even q := by rw [hq_eq]; exact hp_odd.add_one
          -- q > 2
          have hq_gt_2 : q > 2 := by omega
          -- An even number > 2 is not prime
          have hq_not_prime : ¬ Nat.Prime q := fun h => by
            have : 2 ∣ q := hq_even.two_dvd
            have h2_eq_q : 2 = q := (Nat.Prime.eq_one_or_self_of_dvd h 2 this).resolve_left (by norm_num)
            omega
          exact hq_not_prime hq_nat

        -- Step 14.3.11: So p = 2 and q = 3
        have hq_eq_3 : q = 3 := by omega

        -- Step 14.3.12: Now |G| = 4 * 3 = 12
        have hG_eq_12 : Fintype.card G = 12 := by simp [hG, hp_eq_2, hq_eq_3]

        -- Step 14.3.13: We have n_3 = p^2 = 4 and n_2 = q = 3
        have hIndex_P_is_3 : P.index = 3 := by simp [hIndexP, hq_eq_3]

        -- Step 14.3.14: Use the action on cosets G/P
        -- First prove that normalCore.index divides factorial of P.index
        have hCoreFactorial : (P : Subgroup G).normalCore.index ∣ Nat.factorial P.index := by
          -- Step 14.3.14.1: identify the kernel with the normal core
          have hKer :
              (P : Subgroup G).normalCore = (MulAction.toPermHom G (G ⧸ (P : Subgroup G))).ker := by
            simp [Subgroup.normalCore_eq_ker (H := (P : Subgroup G))]
          -- Step 14.3.14.2: relate the index of the kernel to the size of the image
          have hIndexKer :
              (P : Subgroup G).normalCore.index =
                Nat.card (MulAction.toPermHom G (G ⧸ (P : Subgroup G))).range := by
            simpa [hKer] using
              (index_ker (MulAction.toPermHom G (G ⧸ (P : Subgroup G))))
          -- Step 14.3.14.3: the image sits inside the full symmetric group
          have hRangeDiv :
              Nat.card (MulAction.toPermHom G (G ⧸ (P : Subgroup G))).range ∣
                Nat.card (Equiv.Perm (G ⧸ (P : Subgroup G))) :=
            card_subgroup_dvd_card _
          -- Step 14.3.14.4: rewrite the divisibility using the identifications above
          have hDiv1 :
              (P : Subgroup G).normalCore.index ∣ Nat.card (Equiv.Perm (G ⧸ (P : Subgroup G))) := by
            simpa [hIndexKer] using hRangeDiv
          have hPermCardNat :
              Nat.card (Equiv.Perm (G ⧸ (P : Subgroup G))) =
                Nat.factorial (Nat.card (G ⧸ (P : Subgroup G))) :=
            Nat.card_perm (α := G ⧸ (P : Subgroup G))
          have hDiv2 :
              (P : Subgroup G).normalCore.index ∣ Nat.factorial (Nat.card (G ⧸ (P : Subgroup G))) := by
            exact hPermCardNat ▸ hDiv1
          -- Step 14.3.14.5: replace the coset count with the subgroup index
          have hIndexCardNat : Nat.card (G ⧸ (P : Subgroup G)) = P.index :=
            (Subgroup.index_eq_card (H := (P : Subgroup G))).symm
          exact hIndexCardNat ▸ hDiv2

        -- Step 14.3.15: The kernel is the normal core of P
        -- By simplicity, either kernel = ⊥ or kernel = ⊤
        have hKernel_normal : (P : Subgroup G).normalCore.Normal := Subgroup.normalCore_normal (P : Subgroup G)
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup G).normalCore hKernel_normal with hKer_bot | hKer_top

        · -- Step 14.3.16: Case kernel = ⊥ (trivial)
          -- Then G embeds into Sym(G/P) ≅ S_3
          -- So |G| divides |S_3| = 3! = 6
          -- But |G| = 12 doesn't divide 6
          have hCoreIndex : (P : Subgroup G).normalCore.index = Fintype.card G := by
            rw [hKer_bot]
            simp only [Subgroup.index_bot, Nat.card_eq_fintype_card]
          have hDivFactorial : Fintype.card G ∣ Nat.factorial P.index := by
            simpa [hCoreIndex] using hCoreFactorial
          have hFactorial : Nat.factorial P.index = 6 := by
            rw [hIndex_P_is_3]
            native_decide
          rw [hFactorial, hG_eq_12] at hDivFactorial
          -- 12 ∣ 6 is false
          norm_num at hDivFactorial

        · -- Step 14.3.17: Case kernel = ⊤ (all of G)
          -- Then normal core = G, so G ≤ P (since normal core ≤ P)
          -- But P has index 3, so P ≠ G
          have hTop_le_P : (⊤ : Subgroup G) ≤ (P : Subgroup G) := by
            rw [← hKer_top]
            exact Subgroup.normalCore_le (P : Subgroup G)
          have hP_eq_top : (P : Subgroup G) = ⊤ := top_unique hTop_le_P
          have hIndex_1 : P.index = 1 := by simp only [hP_eq_top, Subgroup.index_top]
          omega
