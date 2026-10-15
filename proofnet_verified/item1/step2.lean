import Mathlib
import Pistis

open Subgroup

/-- Given the normal forms of segment 1.1 (`step1`) together with the commutativity hypothesis
`a * b = b * a`, any two elements of the subgroup commute:
`gh = a^i b^j a^k b^l = a^k b^l a^i b^j = hg`. This is the content of segment 1.2. -/
theorem helper_Artin_exercise_2_2_9_step2 {G : Type*} [Group G] {a b : G}
    (step1 : ∀ g h : closure {x | x = a ∨ x = b},
      ∃ i j k l : ℤ, (g : G) = a ^ i * b ^ j ∧ (h : G) = a ^ k * b ^ l)
    (hcomm : a * b = b * a) :
    ∀ g h : closure {x | x = a ∨ x = b}, g * h = h * g := by
  have hab : Commute a b := hcomm
  intro g h
  -- Write `g = a^i b^j` and `h = a^k b^l` using segment 1.1.
  obtain ⟨i, j, k, l, hg, hh⟩ := step1 g h
  -- The two normal forms commute because all powers of `a` and `b` commute.
  have hpow : Commute (a ^ i * b ^ j) (a ^ k * b ^ l) := by
    have h_aa : Commute (a ^ i) (a ^ k) := (Commute.refl a).zpow_zpow i k
    have h_ab : Commute (a ^ i) (b ^ l) := hab.zpow_zpow i l
    have h_ba : Commute (b ^ j) (a ^ k) := hab.symm.zpow_zpow j k
    have h_bb : Commute (b ^ j) (b ^ l) := (Commute.refl b).zpow_zpow j l
    exact (h_aa.mul_left h_ba).mul_right (h_ab.mul_left h_bb)
  -- Transport the equality in `G` back to the subgroup.
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [hg, hh]
  exact hpow.eq
