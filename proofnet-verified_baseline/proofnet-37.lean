import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that $G$ cannot have a subgroup $H$ with $|H|=n-1$, where $n=|G|>2$.
-/

/-Informal Proof

Solution: Under these conditions, there exists a nonidentity element $x \in H$ and an element $y \notin H$. Consider the product $x y$. If $x y \in H$, then since $x^{-1} \in H$ and $H$ is a subgroup, $y \in H$, a contradiction. If $x y \notin H$, then we have $x y=y$. Thus $x=1$, a contradiction. Thus no such subgroup exists.
-/

theorem Dummit_Foote_exercise_2_1_5 {G : Type*} [Group G] [Fintype G]
  (hG : card G > 2) (H : Subgroup G) [Fintype H] :
  card H ≠ card G - 1 := by
  classical
  -- Step 1: Assume, for contradiction, that the subgroup has size `card G - 1`.
  intro h
  -- Step 2: Invoke Lagrange’s theorem to relate the two cardinalities via the index.
  have hprod : (card G - 1) * H.index = card G := by
    simpa [h] using H.card_mul_index
  -- Step 3: Record the numeric hypothesis `2 < card G`.
  have hG_gt_two : 2 < card G := by
    simpa using hG
  -- Step 4: Note useful basic inequalities that follow from the size of `G`.
  have hG_pos : 0 < card G :=
    lt_trans (lt_trans Nat.zero_lt_one (Nat.succ_lt_succ Nat.zero_lt_one)) hG_gt_two
  have hG_ge_one : 1 ≤ card G := Nat.succ_le_of_lt hG_pos
  -- Step 5: Record that `card G - 1` divides `card G` thanks to the product identity.
  have h_dvd : card G - 1 ∣ card G := ⟨H.index, hprod.symm⟩
  -- Step 6: Consecutive natural numbers are coprime, which we express explicitly here.
  have h_le : card G - 1 ≤ card G := Nat.sub_le (card G) 1
  have h_one : card G - (card G - 1) = 1 := by
    have hsum : (card G - 1) + 1 = card G := Nat.sub_add_cancel hG_ge_one
    simpa [hsum] using Nat.add_sub_cancel_left (card G - 1) 1
  have h_gcd : Nat.gcd (card G) (card G - 1) = 1 := by
    calc
      Nat.gcd (card G) (card G - 1)
          = Nat.gcd (card G) (card G - (card G - 1)) :=
            (Nat.gcd_self_sub_right h_le).symm
      _ = Nat.gcd (card G) 1 := by simp [h_one]
      _ = 1 := by simp
  have hcoprime' :
      Nat.Coprime (card G) (card G - 1) :=
    (Nat.coprime_iff_gcd_eq_one).2 h_gcd
  have hcoprime :
      Nat.Coprime (card G - 1) (card G) := by
    simpa [Nat.coprime_comm] using hcoprime'
  -- Step 7: A number dividing two coprime integers must equal one, hence `card G - 1 = 1`.
  have hminus_one_eq_one : card G - 1 = 1 :=
    Nat.eq_one_of_dvd_coprimes hcoprime dvd_rfl h_dvd
  -- Step 8: Rewrite the size of `G` using the previous equality, obtaining `card G = 2`.
  have hG_eq_two : card G = 2 := by
    calc
      card G = (card G - 1) + 1 := (Nat.sub_add_cancel hG_ge_one).symm
      _ = 1 + 1 := by simp [hminus_one_eq_one]
      _ = 2 := by decide
  -- Step 9: The numeric hypothesis `2 < card G` now contradicts `card G = 2`.
  have : (2 : ℕ) < 2 := by simp [hG_eq_two] at hG_gt_two
  exact (lt_irrefl (2 : ℕ)) this
