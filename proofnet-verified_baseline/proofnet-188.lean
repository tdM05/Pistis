import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators



/-Informal Statement

Prove that no group of order $p q$, where $p$ and $q$ are prime, is simple.
-/

/-Informal Proof

If $|G|=n=p q$ then the only two Sylow subgroups are of order $p$ and $q$.
From Sylow's third theorem we know that $n_p \mid q$ which means that $n_p=1$ or $n_p=q$.
If $n_p=1$ then we are done (by a corollary of Sylow's theorem)
If $n_p=q$ then we have accounted for $q(p-1)=p q-q$ elements of $G$ and so there is only one group of order $q$ and again we are done.
-/

theorem Artin_exercise_6_4_2 {G : Type*} [Group G] [Fintype G] {p q : ℕ}
  (hp : Nat.Prime p) (hq : Nat.Prime q) (hG : card G = p*q) :
  IsSimpleGroup G → false := by
  /-
  **Overview of the proof:**
  We prove that no group of order p*q (where p, q are primes) is simple.

  **Case 1: p = q**
  Then |G| = p², and G is a p-group. By the fact that p-groups have nontrivial
  center, G has a nontrivial center. If G were simple, Z(G) would be ⊥ or ⊤.
  Since Z(G) is nontrivial, Z(G) ≠ ⊥. If Z(G) = ⊤, then G is abelian, and any
  subgroup of order p (which exists) is normal and proper, contradicting simplicity.

  **Case 2: p ≠ q**
  WLOG assume p < q. By Sylow's third theorem:
  - n_q ≡ 1 (mod q) and n_q | p*q / q = p
  Since p < q and n_q ≡ 1 (mod q), we must have n_q = 1.
  Thus there's a unique Sylow q-subgroup, which is normal and has order q.
  This gives a proper nontrivial normal subgroup, contradicting simplicity.

  If p > q, the same argument applies with p and q swapped.
  -/
  classical
  -- Step 1: Assume G is simple and derive a contradiction.
  -- The goal is `false`, which is `False.elim False`.
  intro hSimple
  haveI := hSimple
  -- Step 1.1: We will derive `False` and use `False.elim` to prove `false`.
  suffices h : False by exact h.elim

  -- Step 2: Set up Fact instances for the prime hypotheses.
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : Fact (Nat.Prime q) := ⟨hq⟩

  -- Step 3: Basic numeric setup.
  -- Step 3.1: |G| as Nat.card.
  have h_card_nat : Nat.card G = p * q := by simpa [Nat.card_eq_fintype_card] using hG

  -- Step 3.2: p and q are positive (primes are ≥ 2).
  have hp_pos : 0 < p := hp.pos
  have hq_pos : 0 < q := hq.pos

  -- Step 3.3: p*q > 0.
  have hpq_pos : 0 < p * q := Nat.mul_pos hp_pos hq_pos

  -- Step 3.4: p and q divide |G|.
  have hp_dvd : p ∣ Nat.card G := by rw [h_card_nat]; exact Dvd.intro q rfl
  have hq_dvd : q ∣ Nat.card G := by rw [h_card_nat]; exact Dvd.intro_left p rfl

  -- Step 4: Get Sylow p and q subgroups.
  obtain ⟨P⟩ := Sylow.nonempty (G := G) (p := p)
  obtain ⟨Q⟩ := Sylow.nonempty (G := G) (p := q)

  -- Step 5: Helper function to derive contradiction from proper nontrivial normal subgroup.
  have contradict_simple : ∀ (H : Subgroup G), H.Normal → H ≠ ⊥ → H ≠ ⊤ → False := by
    intro H hNormal hNeBot hNeTop
    rcases hSimple.eq_bot_or_eq_top_of_normal H hNormal with h | h
    · exact hNeBot h
    · exact hNeTop h

  -- Step 6: Establish Sylow subgroup cardinalities.
  -- Step 6.2: Sylow p-subgroup is nontrivial (since p | |G|).
  have hP_ne_bot : (P : Subgroup G) ≠ ⊥ := P.ne_bot_of_dvd_card hp_dvd

  -- Step 6.3: Sylow q-subgroup is nontrivial (since q | |G|).
  have hQ_ne_bot : (Q : Subgroup G) ≠ ⊥ := Q.ne_bot_of_dvd_card hq_dvd

  -- Step 8: Main case analysis on whether p = q or p ≠ q.
  by_cases hpq : p = q

  -- **Case 1: p = q (so |G| = p²)**
  · -- Step 8.1: In this case, |G| = p², so G is a p-group.
    -- We substitute q with p to work uniformly.
    subst hpq

    -- Step 8.1.1: Compute |G| = p².
    have hG_card_sq : Fintype.card G = p ^ 2 := by rw [hG, sq]
    have hG_card_nat_sq : Nat.card G = p ^ 2 := by
      rw [Nat.card_eq_fintype_card, hG_card_sq]

    -- Step 8.1.2: G is nontrivial since |G| = p² ≥ 4.
    have hG_card_ge_4 : Fintype.card G ≥ 4 := by
      rw [hG_card_sq]
      have hp_ge_2 := hp.two_le
      calc p ^ 2 = p * p := sq p
        _ ≥ 2 * 2 := Nat.mul_le_mul hp_ge_2 hp_ge_2
        _ = 4 := by norm_num

    have hG_nontrivial : Nontrivial G := by
      rw [← Fintype.one_lt_card_iff_nontrivial]
      omega
    haveI := hG_nontrivial

    -- Step 8.1.3: G is a p-group (since |G| = p² is a prime power).
    have hG_pGroup : IsPGroup p G := by
      rw [IsPGroup.iff_card]
      exact ⟨2, hG_card_nat_sq⟩

    -- Step 8.1.5: The center of G is nontrivial.
    have hCenter_nontrivial : Nontrivial (Subgroup.center G) := hG_pGroup.center_nontrivial

    -- Step 8.1.6: center ≠ ⊥.
    have hCenter_ne_bot : Subgroup.center G ≠ ⊥ := by
      intro h
      rw [h] at hCenter_nontrivial
      exact not_nontrivial (⊥ : Subgroup G) hCenter_nontrivial

    -- Step 8.1.7: The center is normal.
    have hCenter_normal : (Subgroup.center G).Normal := inferInstance

    -- Step 8.1.8: By simplicity, center must be ⊤.
    have hCenter_top : Subgroup.center G = ⊤ := by
      rcases hSimple.eq_bot_or_eq_top_of_normal _ hCenter_normal with h | h
      · exact (hCenter_ne_bot h).elim
      · exact h

    -- Step 8.1.9: G is abelian (center = G).
    have hG_abelian : ∀ a b : G, a * b = b * a := by
      intro a b
      have ha : a ∈ Subgroup.center G := by rw [hCenter_top]; trivial
      exact ((Subgroup.mem_center_iff).mp ha b).symm

    -- Step 8.1.10: Find a proper nontrivial subgroup.
    obtain ⟨g, hg_ne_one⟩ : ∃ g : G, g ≠ 1 := exists_ne 1

    -- Step 8.1.11: orderOf g divides |G| = p², so orderOf g ∈ {1, p, p²}.
    have h_ord_dvd : orderOf g ∣ Fintype.card G := orderOf_dvd_card
    rw [hG_card_sq] at h_ord_dvd

    -- Step 8.1.12: Since g ≠ 1, orderOf g ≠ 1.
    have h_ord_ne_1 : orderOf g ≠ 1 := by
      intro h
      have : g = 1 := orderOf_eq_one_iff.mp h
      exact hg_ne_one this

    -- Step 8.1.13: orderOf g = p or p².
    have h_ord_cases : orderOf g = p ∨ orderOf g = p ^ 2 := by
      -- The divisors of p² are 1, p, p² (since p is prime).
      have h_ord_pos : 0 < orderOf g := orderOf_pos g
      have h_ord_le : orderOf g ≤ p ^ 2 := Nat.le_of_dvd (pow_pos hp_pos 2) h_ord_dvd
      -- orderOf g divides p², and orderOf g ≠ 1, so orderOf g = p or p².
      -- Since p is prime, divisors of p² are {1, p, p²}.
      -- Use nat divisibility lemmas.
      have h_dvd_sq : orderOf g ∣ p * p := by simp only [sq] at h_ord_dvd; exact h_ord_dvd
      -- Check if p divides orderOf g
      by_cases hp_dvd_ord : p ∣ orderOf g
      · -- p divides orderOf g
        -- So orderOf g / p divides p
        have h_quot_dvd : orderOf g / p ∣ p := by
          have h1 : orderOf g / p * p = orderOf g := Nat.div_mul_cancel hp_dvd_ord
          have h2 : orderOf g / p * p ∣ p * p := by rw [h1]; exact h_dvd_sq
          exact Nat.dvd_of_mul_dvd_mul_right hp_pos h2
        rcases hp.eq_one_or_self_of_dvd _ h_quot_dvd with h1 | hp'
        · left
          have heq : orderOf g / p * p = orderOf g := Nat.div_mul_cancel hp_dvd_ord
          rw [h1, one_mul] at heq
          exact heq.symm
        · right
          have heq : orderOf g / p * p = orderOf g := Nat.div_mul_cancel hp_dvd_ord
          rw [hp'] at heq
          simp only [sq]
          exact heq.symm
      · -- p does not divide orderOf g
        -- Then orderOf g is coprime to p, so orderOf g | 1 (since orderOf g | p²)
        have h_coprime : Nat.Coprime (orderOf g) p := by
          exact (hp.coprime_iff_not_dvd.mpr hp_dvd_ord).symm
        have h_coprime_sq : Nat.Coprime (orderOf g) (p ^ 2) := by
          exact h_coprime.pow_right 2
        -- orderOf g | p² and gcd(orderOf g, p²) = 1
        -- So orderOf g = 1
        have h_eq_1 : orderOf g = 1 := by
          -- If a | b and gcd(a, b) = 1, then a = 1
          rw [Nat.Coprime] at h_coprime_sq
          have h_dvd_gcd : orderOf g ∣ Nat.gcd (orderOf g) (p ^ 2) := Nat.dvd_gcd (dvd_refl _) h_ord_dvd
          rw [h_coprime_sq] at h_dvd_gcd
          exact Nat.eq_one_of_dvd_one h_dvd_gcd
        exact (h_ord_ne_1 h_eq_1).elim

    -- Step 8.1.14: Define the proper nontrivial subgroup and derive contradiction.
    rcases h_ord_cases with hord_p | hord_psq

    -- Case: orderOf g = p.
    · -- ⟨g⟩ has order p, which is nontrivial (p ≥ 2 > 1) and proper (p < p²).
      have hH_ne_bot : zpowers g ≠ ⊥ := by
        intro hbot
        rw [eq_bot_iff] at hbot
        have : g ∈ (⊥ : Subgroup G) := hbot (Subgroup.mem_zpowers g)
        simp only [Subgroup.mem_bot] at this
        exact hg_ne_one this

      have hH_ne_top : zpowers g ≠ ⊤ := by
        intro htop
        have h1 : Nat.card (zpowers g) = Nat.card G := by simp [htop]
        rw [Nat.card_zpowers, hord_p, h_card_nat] at h1
        -- h1 : p = p * p
        have hp_ge_2 := hp.two_le
        have : p * p ≥ p * 2 := Nat.mul_le_mul_left p hp_ge_2
        have : p * 2 > p := by omega
        omega

      -- zpowers g is normal (since G is abelian).
      have hH_normal : (zpowers g).Normal := by
        constructor
        intro n hn x
        have heq : x * n * x⁻¹ = n := by
          have hcomm := hG_abelian x n
          calc x * n * x⁻¹ = n * x * x⁻¹ := by rw [hcomm]
            _ = n * (x * x⁻¹) := by rw [mul_assoc]
            _ = n * 1 := by rw [mul_inv_cancel]
            _ = n := by rw [mul_one]
        rw [heq]
        exact hn

      exact contradict_simple (zpowers g) hH_normal hH_ne_bot hH_ne_top

    -- Case: orderOf g = p².
    · -- g generates G (cyclic). Consider g^p, which has order p.
      -- ⟨g^p⟩ has order p, which is nontrivial and proper.
      have hgp_ord : orderOf (g ^ p) = p := by
        rw [orderOf_pow g, hord_psq]
        have h1 : Nat.gcd (p ^ 2) p = p := by
          have h2 : p ^ 2 = p * p := sq p
          rw [h2, Nat.gcd_comm]
          -- gcd(p, p * p) = p
          -- Since p | p * p, we have gcd(p, p * p) = p
          exact Nat.gcd_eq_left (dvd_mul_right p p)
        rw [h1]
        simp only [sq]
        exact Nat.mul_div_left p hp_pos

      have hH_ne_bot : zpowers (g ^ p) ≠ ⊥ := by
        intro hbot
        rw [eq_bot_iff] at hbot
        have : g ^ p ∈ (⊥ : Subgroup G) := hbot (Subgroup.mem_zpowers (g ^ p))
        simp only [Subgroup.mem_bot] at this
        have h_ord_1 : orderOf (g ^ p) = 1 := orderOf_eq_one_iff.mpr this
        rw [hgp_ord] at h_ord_1
        exact hp.ne_one h_ord_1

      have hH_ne_top : zpowers (g ^ p) ≠ ⊤ := by
        intro htop
        have h1 : Nat.card (zpowers (g ^ p)) = Nat.card G := by simp [htop]
        rw [Nat.card_zpowers, hgp_ord, h_card_nat] at h1
        -- h1 : p = p * p
        have hp_ge_2 := hp.two_le
        have : p * p ≥ p * 2 := Nat.mul_le_mul_left p hp_ge_2
        have : p * 2 > p := by omega
        omega

      -- zpowers (g^p) is normal (since G is abelian).
      have hH_normal : (zpowers (g ^ p)).Normal := by
        constructor
        intro n hn x
        have heq : x * n * x⁻¹ = n := by
          have hcomm := hG_abelian x n
          calc x * n * x⁻¹ = n * x * x⁻¹ := by rw [hcomm]
            _ = n * (x * x⁻¹) := by rw [mul_assoc]
            _ = n * 1 := by rw [mul_inv_cancel]
            _ = n := by rw [mul_one]
        rw [heq]
        exact hn

      exact contradict_simple (zpowers (g ^ p)) hH_normal hH_ne_bot hH_ne_top

  -- **Case 2: p ≠ q (so |G| = p*q with p ≠ q)**
  · -- Step 9: WLOG assume p < q or p > q.
    -- In either case, one Sylow subgroup is unique hence normal.

    -- Step 9.1: Either p < q or q < p (since p ≠ q).
    rcases Nat.lt_trichotomy p q with hp_lt_q | hp_eq_q | hq_lt_p

    · -- Step 9.2: Case p < q.
      -- n_q ≡ 1 (mod q) and n_q | p (since n_q | |G|/|Q| = |G|/q = p).
      -- Since p < q and n_q ≥ 1, and n_q ≡ 1 (mod q) means n_q = 1 or n_q ≥ q + 1 > p.
      -- So n_q = 1, meaning Q is the unique Sylow q-subgroup, hence normal.

      -- Step 9.2.1: Compute the number of Sylow q-subgroups.
      set nq : ℕ := Nat.card (Sylow q G) with hnq_def

      -- Step 9.2.2: n_q ≡ 1 (mod q).
      have h_nq_mod : nq ≡ 1 [MOD q] := card_sylow_modEq_one (p := q) (G := G)

      -- Step 9.2.3: n_q | [G : Q] = |G| / |Q|.
      -- First, compute |Q|. Since q^1 || p*q (as p ≠ q), |Q| = q.
      have hQ_card : Nat.card Q.toSubgroup = q := by
        have h := Sylow.card_eq_multiplicity (G := G) (p := q) Q
        have hFactor : Nat.factorization (Nat.card G) q = 1 := by
          rw [h_card_nat]
          have : Nat.factorization (p * q) q = 1 := by
            rw [Nat.factorization_mul (Nat.Prime.ne_zero hp) (Nat.Prime.ne_zero hq)]
            simp only [Finsupp.coe_add, Pi.add_apply]
            have hfp : Nat.factorization p q = 0 := by
              rw [Nat.factorization_eq_zero_iff]
              -- Need to show ¬q.Prime ∨ ¬q ∣ p ∨ p = 0
              -- We show ¬q ∣ p (the middle disjunct)
              right; left
              intro hdvd
              -- hdvd : q ∣ p
              -- If q | p and both are prime, then p = q (since p is prime, its divisors are 1 and p)
              rcases hp.eq_one_or_self_of_dvd q hdvd with h1 | hpq''
              · exact hq.ne_one h1
              · exact hpq hpq''.symm
            have hfq : Nat.factorization q q = 1 := hq.factorization_self
            rw [hfp, hfq]
          exact this
        rw [h, hFactor, pow_one]

      -- Step 9.2.4: n_q | [G : Q] = p (since |G| = p*q and |Q| = q).
      have h_nq_dvd : nq ∣ p := by
        have h1 : nq ∣ Nat.card G := by
          have h2 : nq ∣ Q.index := Sylow.card_dvd_index Q
          exact h2.trans Q.1.index_dvd_card
        have h2 : nq ∣ p * q := by rwa [h_card_nat] at h1
        have h3 : Nat.Coprime nq q := by
          have h := not_dvd_card_sylow (p := q) (G := G)
          exact (hq.coprime_iff_not_dvd).2 h |>.symm
        exact h3.dvd_of_dvd_mul_right h2

      -- Step 9.2.5: Since n_q | p and p is prime, n_q ∈ {1, p}.
      -- Since n_q ≡ 1 (mod q) and p < q, we have n_q < q (if n_q = p) or n_q = 1.
      -- If n_q = p, then since n_q ≡ 1 (mod q), p ≡ 1 (mod q), so q | p - 1.
      -- But p < q, so p - 1 < q - 1 < q, so q ∤ (p - 1) unless p - 1 = 0, i.e., p = 1, impossible.
      -- Hence n_q = 1.
      have h_nq_eq_1 : nq = 1 := by
        cases' hp.eq_one_or_self_of_dvd nq h_nq_dvd with h h
        · exact h
        · -- n_q = p, so p ≡ 1 (mod q).
          exfalso
          have h_p_mod : p ≡ 1 [MOD q] := by
            rw [h] at h_nq_mod
            exact h_nq_mod
          -- p ≡ 1 (mod q) means q | (p - 1).
          have h_q_dvd : q ∣ p - 1 := by
            unfold Nat.ModEq at h_p_mod
            have hp_ge_2 := hp.two_le
            have hq_ge_2 := hq.two_le
            have h1pq : 1 % q = 1 := Nat.mod_eq_of_lt (by omega : 1 < q)
            rw [h1pq] at h_p_mod
            -- p % q = 1, so p = q * k + 1 for some k
            -- Since p < q, we have p % q = p, so p = 1, contradiction.
            -- Actually, if p < q then p % q = p, so p = 1, contradiction with hp.two_le
            have h_p_mod_eq : p % q = p := Nat.mod_eq_of_lt hp_lt_q
            rw [h_p_mod_eq] at h_p_mod
            -- p = 1, contradiction
            omega
          -- But p < q, so p - 1 < q, so q cannot divide p - 1 unless p - 1 = 0.
          have h_p_sub_1_lt_q : p - 1 < q := by omega
          have h_p_ne_1 : p ≠ 1 := hp.ne_one
          have h_p_sub_1_ne_0 : p - 1 ≠ 0 := by omega
          have : q ≤ p - 1 := Nat.le_of_dvd (Nat.pos_of_ne_zero h_p_sub_1_ne_0) h_q_dvd
          omega

      -- Step 9.2.6: n_q = 1 means Q is the unique Sylow q-subgroup, hence normal.
      have hQ_normal : Q.Normal := by
        have hss : Subsingleton (Sylow q G) := by
          have := Nat.card_eq_one_iff_unique.mp h_nq_eq_1
          exact this.1
        exact Sylow.normal_of_subsingleton (p := q) (G := G) Q

      -- Step 9.2.7: Q is proper (|Q| = q < p*q = |G|).
      have hQ_ne_top : (Q : Subgroup G) ≠ ⊤ := by
        intro htop
        have h1 : Nat.card ↥(Q : Subgroup G) = Nat.card G := by simp [htop]
        rw [hQ_card, h_card_nat] at h1
        -- h1 : q = p * q, so p = 1, contradiction
        have h2 : p * q = q := h1.symm
        have h3 : p = 1 := by
          -- Rewrite q = 1 * q to get p * q = 1 * q
          have h2' : p * q = 1 * q := by simp [h2]
          exact Nat.eq_of_mul_eq_mul_right hq_pos h2'
        exact hp.ne_one h3

      -- Step 9.2.8: Contradiction.
      exact contradict_simple (Q : Subgroup G) hQ_normal hQ_ne_bot hQ_ne_top

    · -- Step 9.3: Case p = q (impossible since we're in the p ≠ q branch).
      exact (hpq hp_eq_q).elim

    · -- Step 9.4: Case q < p. Same argument with roles of p and q swapped.
      -- n_p ≡ 1 (mod p) and n_p | q. Since q < p and n_p ≡ 1 (mod p), n_p = 1.

      -- Step 9.4.1: Compute the number of Sylow p-subgroups.
      set np : ℕ := Nat.card (Sylow p G) with hnp_def

      -- Step 9.4.2: n_p ≡ 1 (mod p).
      have h_np_mod : np ≡ 1 [MOD p] := card_sylow_modEq_one (p := p) (G := G)

      -- Step 9.4.3: Compute |P| = p.
      have hP_card : Nat.card P.toSubgroup = p := by
        have h := Sylow.card_eq_multiplicity (G := G) (p := p) P
        have hFactor : Nat.factorization (Nat.card G) p = 1 := by
          rw [h_card_nat]
          have : Nat.factorization (p * q) p = 1 := by
            rw [Nat.factorization_mul (Nat.Prime.ne_zero hp) (Nat.Prime.ne_zero hq)]
            simp only [Finsupp.coe_add, Pi.add_apply]
            have hfp : Nat.factorization p p = 1 := hp.factorization_self
            have hfq : Nat.factorization q p = 0 := by
              rw [Nat.factorization_eq_zero_iff]
              -- Need to show ¬p.Prime ∨ ¬p ∣ q ∨ q = 0
              -- We show ¬p ∣ q (the middle disjunct)
              right; left
              intro hdvd
              -- hdvd : p ∣ q
              -- If p | q and both are prime, then p = q (since q is prime, its divisors are 1 and q)
              rcases hq.eq_one_or_self_of_dvd p hdvd with h1 | hpq'
              · exact hp.ne_one h1
              · exact hpq hpq'
            rw [hfp, hfq]
          exact this
        rw [h, hFactor, pow_one]

      -- Step 9.4.4: n_p | q.
      have h_np_dvd : np ∣ q := by
        have h1 : np ∣ Nat.card G := by
          have h2 : np ∣ P.index := Sylow.card_dvd_index P
          exact h2.trans P.1.index_dvd_card
        have h2 : np ∣ p * q := by rwa [h_card_nat] at h1
        have h3 : Nat.Coprime np p := by
          have h := not_dvd_card_sylow (p := p) (G := G)
          exact (hp.coprime_iff_not_dvd).2 h |>.symm
        exact h3.dvd_of_dvd_mul_left h2

      -- Step 9.4.5: n_p = 1.
      have h_np_eq_1 : np = 1 := by
        cases' hq.eq_one_or_self_of_dvd np h_np_dvd with h h
        · exact h
        · exfalso
          -- np = q, so q ≡ 1 (mod p)
          have h_q_mod : q ≡ 1 [MOD p] := by
            have h' := h_np_mod
            simp only [h] at h'
            exact h'
          -- q ≡ 1 (mod p) and q < p leads to contradiction
          -- Since q < p, we have q % p = q
          -- From q ≡ 1 (mod p), we get q % p = 1 % p = 1
          -- So q = 1, contradicting q being prime
          unfold Nat.ModEq at h_q_mod
          have hp_ge_2 := hp.two_le
          have h1_mod_p : 1 % p = 1 := Nat.mod_eq_of_lt (by omega : 1 < p)
          have h_q_mod_eq : q % p = q := Nat.mod_eq_of_lt hq_lt_p
          rw [h1_mod_p, h_q_mod_eq] at h_q_mod
          -- h_q_mod : q = 1, but q is prime so q ≥ 2
          have hq_ge_2 := hq.two_le
          omega

      -- Step 9.4.6: P is normal.
      have hP_normal : P.Normal := by
        have hss : Subsingleton (Sylow p G) := by
          have := Nat.card_eq_one_iff_unique.mp h_np_eq_1
          exact this.1
        exact Sylow.normal_of_subsingleton (p := p) (G := G) P

      -- Step 9.4.7: P is proper.
      have hP_ne_top : (P : Subgroup G) ≠ ⊤ := by
        intro htop
        have h1 : Nat.card ↥(P : Subgroup G) = Nat.card G := by simp [htop]
        rw [hP_card, h_card_nat] at h1
        -- h1 : p = p * q, so p * q = p
        have h2 : p * q = p := h1.symm
        -- p * q = p * 1
        have h2' : p * q = p * 1 := by simp [h2]
        have : q = 1 := Nat.eq_of_mul_eq_mul_left hp_pos h2'
        exact hq.ne_one this

      -- Step 9.4.8: Contradiction.
      exact contradict_simple (P : Subgroup G) hP_normal hP_ne_bot hP_ne_top
