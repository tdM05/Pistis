import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Let $G$ be a finite group of composite order $n$ with the property that $G$ has a subgroup of order $k$ for each positive integer $k$ dividing $n$. Prove that $G$ is not simple.
-/

/-Informal Proof

Solution: Let $p$ be the smallest prime dividing $n$, and write $n=p m$. Now $G$ has a subgroup $H$ of order $m$, and $H$ has index $p$. Then $H$ is normal in $G$.
-/

theorem Dummit_Foote_exercise_4_2_14 {G : Type*} [Fintype G] [Group G]
  (hG : ¬ (card G).Prime) (hG1 : ∀ k : ℕ, k ∣ card G →
  ∃ (H : Subgroup G) (fH : Fintype H), @card H fH = k) :
  ¬ IsSimpleGroup G := by
  classical
  -- Step 0: Argue by contradiction and use the simplicity hypothesis as a typeclass instance.
  intro hsimple
  haveI : IsSimpleGroup G := hsimple

  -- Step 1: A simple group is nontrivial, hence its cardinality is strictly larger than 1.
  have hcard_ne_one : Fintype.card G ≠ 1 := by
    -- Step 1.1: Simplicity gives nontriviality.
    have hnontriv : Nontrivial G := inferInstance
    -- Step 1.2: Nontrivial finite type ⇒ card > 1.
    have hgt : 1 < Fintype.card G :=
      (Fintype.one_lt_card_iff_nontrivial).2 hnontriv
    -- Step 1.3: Convert the strict inequality into the desired disequality.
    exact ne_of_gt hgt

  -- Step 2: Define the smallest prime factor `p` of |G| and the complementary factor `k`.
  set p : ℕ := (Fintype.card G).minFac with hp_def
  set k : ℕ := Fintype.card G / p with hk_def

  -- Step 3: Collect arithmetic facts about `p` and `k`.
  have hp_prime : Nat.Prime p := by
    -- Step 3.1: minFac of a non‑unit number is prime.
    dsimp [p] at hcard_ne_one
    exact Nat.minFac_prime hcard_ne_one
  have hp_dvd : p ∣ Fintype.card G := by
    -- Step 3.2: minFac always divides the number it is computed from.
    dsimp [p]; exact Nat.minFac_dvd _
  have hcard_mul : p * k = Fintype.card G := by
    -- Step 3.3: Re-express |G| = p * k using the divisibility above.
    have : k * p = Fintype.card G := by
      dsimp [k, p]; exact Nat.div_mul_cancel hp_dvd
    -- Step 3.4: Commute the product to match the chosen order.
    simpa [Nat.mul_comm] using this

  -- Step 4: Use the hypothesis to pick a subgroup `H` whose order is `k`.
  obtain ⟨H, fH, hcardH⟩ :=
    hG1 k (by exact ⟨p, by simpa [Nat.mul_comm] using hcard_mul.symm⟩)
  -- Step 4.1: Equip `H` with the provided fintype structure.
  let _ : Fintype H := fH
  -- Step 4.2: Simplify the cardinality statement of `H`.
  have hcardH' : Fintype.card H = k := by simpa using hcardH

  -- Step 5: Compute the index of `H` and show it equals `p`.
  have hindex_mul : H.index * k = Fintype.card G := by
    -- Step 5.1: Substitute the known value of |H| into `index_mul_card`.
    calc
      H.index * k = H.index * Fintype.card H := by simp [hcardH']
      _ = Fintype.card G := by
        -- `index_mul_card` is stated with `Nat.card`; rewrite via `Nat.card_eq_fintype_card`.
        simpa [Nat.card_eq_fintype_card] using (Subgroup.index_mul_card (H := H))

  have hk_pos : 0 < k := by
    -- Step 5.2: `k` is positive because |G| > 0 and `p` is positive.
    dsimp [k]
    have hcard_pos : 0 < Fintype.card G :=
      Fintype.card_pos_iff.mpr ⟨(1 : G)⟩
    have hp_pos : 0 < p := hp_prime.pos
    have hp_le_card : p ≤ Fintype.card G :=
      Nat.le_of_dvd hcard_pos hp_dvd
    exact Nat.div_pos hp_le_card hp_pos

  have hk_ne_zero : k ≠ 0 := Nat.ne_of_gt hk_pos

  have hk_ne_one : k ≠ 1 := by
    -- Step 5.3: If `k = 1`, then |G| = p would be prime, contradicting `hG`.
    intro hk1
    have hcard_eq_p : Fintype.card G = p := by
      simpa [hk1, Nat.mul_one] using hcard_mul.symm
    have hcard_prime : (Fintype.card G).Prime := by
      simpa [hcard_eq_p] using hp_prime
    exact hG hcard_prime

  have hk_gt_one : 1 < k :=
    Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hk_ne_zero, hk_ne_one⟩

  have hindex_eq_p : H.index = p := by
    -- Step 5.4: Cancel `k` from the equality `H.index * k = p * k`.
    have hindex_mul' : H.index * k = p * k := by
      calc
        H.index * k = Fintype.card G := hindex_mul
        _ = p * k := hcard_mul.symm
    exact Nat.mul_right_cancel hk_pos hindex_mul'

  have hindex_minFac : H.index = (Nat.card G).minFac := by
    -- Step 5.5: Rewrite `p` back as the smallest prime factor of `Nat.card G`.
    have hindex_eq_minFac_fintype : H.index = (Fintype.card G).minFac := by
      simpa [p] using hindex_eq_p
    simpa [Nat.card_eq_fintype_card] using hindex_eq_minFac_fintype

  have hnormal : H.Normal :=
    Subgroup.normal_of_index_eq_minFac_card (G := G) (H := H) hindex_minFac

  -- Step 6: Show that `H` is proper (neither bottom nor top).
  have hH_ne_top : H ≠ ⊤ := by
    -- Step 6.1: Index 1 characterizes `⊤`; here the index is the prime `p ≥ 2`.
    intro htop
    have hindex_one : H.index = 1 := by
      simp [htop]
    have hp_ne_one : p ≠ 1 := hp_prime.ne_one
    exact hp_ne_one (by simpa [hindex_eq_p] using hindex_one)

  have hH_ne_bot : H ≠ ⊥ := by
    -- Step 6.2: Cardinality strictly bigger than 1 forces `H ≠ ⊥`.
    have hcardH_nat : 1 < Nat.card H := by
      simpa [Nat.card_eq_fintype_card, hcardH'] using hk_gt_one
    exact (Subgroup.one_lt_card_iff_ne_bot (H := H)).1 hcardH_nat

  -- Step 7: Contradict simplicity using the existence of a proper nontrivial normal subgroup.
  have hsimple_contr :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (H := H) hnormal)
  cases hsimple_contr with
  | inl hbot => exact hH_ne_bot hbot
  | inr htop => exact hH_ne_top htop


/-
The original formalization above translates "composite" as `¬ (card G).Prime`,
which is satisfied by `card G = 1` (since 1 is not prime) — but `1` is not
composite either. The corrected version below adds `card G ≠ 1` so the
hypothesis really does encode "composite order".
-/

theorem Dummit_Foote_exercise_4_2_14_corrected {G : Type*} [Fintype G] [Group G]
  (hG : ¬ (card G).Prime) (hG_ne_one : card G ≠ 1)
  (hG1 : ∀ k : ℕ, k ∣ card G →
    ∃ (H : Subgroup G) (fH : Fintype H), @card H fH = k) :
  ¬ IsSimpleGroup G := by
  classical
  intro hsimple
  haveI : IsSimpleGroup G := hsimple
  -- Simplicity ⇒ nontrivial ⇒ card G > 1 (so the new `hG_ne_one` is implied,
  -- but is still required to make the statement faithful).
  have hcard_ne_one : Fintype.card G ≠ 1 := hG_ne_one
  -- Smallest prime factor `p` of |G|, complementary factor `k = |G|/p`.
  set p : ℕ := (Fintype.card G).minFac with hp_def
  set k : ℕ := Fintype.card G / p with hk_def
  have hp_prime : Nat.Prime p := by
    dsimp [p] at hcard_ne_one
    exact Nat.minFac_prime hcard_ne_one
  have hp_dvd : p ∣ Fintype.card G := by
    dsimp [p]; exact Nat.minFac_dvd _
  have hcard_mul : p * k = Fintype.card G := by
    have : k * p = Fintype.card G := by
      dsimp [k, p]; exact Nat.div_mul_cancel hp_dvd
    simpa [Nat.mul_comm] using this
  -- Use the divisor hypothesis to obtain `H` of order `k`.
  obtain ⟨H, fH, hcardH⟩ :=
    hG1 k (by exact ⟨p, by simpa [Nat.mul_comm] using hcard_mul.symm⟩)
  let _ : Fintype H := fH
  have hcardH' : Fintype.card H = k := by simpa using hcardH
  -- Index of `H` is `p`.
  have hindex_mul : H.index * k = Fintype.card G := by
    calc
      H.index * k = H.index * Fintype.card H := by simp [hcardH']
      _ = Fintype.card G := by
        simpa [Nat.card_eq_fintype_card] using (Subgroup.index_mul_card (H := H))
  have hk_pos : 0 < k := by
    dsimp [k]
    have hcard_pos : 0 < Fintype.card G :=
      Fintype.card_pos_iff.mpr ⟨(1 : G)⟩
    have hp_pos : 0 < p := hp_prime.pos
    have hp_le_card : p ≤ Fintype.card G :=
      Nat.le_of_dvd hcard_pos hp_dvd
    exact Nat.div_pos hp_le_card hp_pos
  have hk_ne_zero : k ≠ 0 := Nat.ne_of_gt hk_pos
  have hk_ne_one : k ≠ 1 := by
    intro hk1
    have hcard_eq_p : Fintype.card G = p := by
      simpa [hk1, Nat.mul_one] using hcard_mul.symm
    have hcard_prime : (Fintype.card G).Prime := by
      simpa [hcard_eq_p] using hp_prime
    exact hG hcard_prime
  have hk_gt_one : 1 < k :=
    Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hk_ne_zero, hk_ne_one⟩
  have hindex_eq_p : H.index = p := by
    have hindex_mul' : H.index * k = p * k := by
      calc
        H.index * k = Fintype.card G := hindex_mul
        _ = p * k := hcard_mul.symm
    exact Nat.mul_right_cancel hk_pos hindex_mul'
  have hindex_minFac : H.index = (Nat.card G).minFac := by
    have hindex_eq_minFac_fintype : H.index = (Fintype.card G).minFac := by
      simpa [p] using hindex_eq_p
    simpa [Nat.card_eq_fintype_card] using hindex_eq_minFac_fintype
  have hnormal : H.Normal :=
    Subgroup.normal_of_index_eq_minFac_card (G := G) (H := H) hindex_minFac
  -- `H` is proper.
  have hH_ne_top : H ≠ ⊤ := by
    intro htop
    have hindex_one : H.index = 1 := by simp [htop]
    have hp_ne_one : p ≠ 1 := hp_prime.ne_one
    exact hp_ne_one (by simpa [hindex_eq_p] using hindex_one)
  have hH_ne_bot : H ≠ ⊥ := by
    have hcardH_nat : 1 < Nat.card H := by
      simpa [Nat.card_eq_fintype_card, hcardH'] using hk_gt_one
    exact (Subgroup.one_lt_card_iff_ne_bot (H := H)).1 hcardH_nat
  cases (IsSimpleGroup.eq_bot_or_eq_top_of_normal (H := H) hnormal) with
  | inl hbot => exact hH_ne_bot hbot
  | inr htop => exact hH_ne_top htop
