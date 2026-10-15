import Mathlib
import Pistis

open Subgroup

/-- Since `a` and `b` commute, for any two elements `g, h` of the subgroup they generate we can
write `g = a ^ i * b ^ j` and `h = a ^ k * b ^ l` for integers `i, j, k, l`. This is the content
of segment 1.1. -/
theorem helper_Artin_exercise_2_2_9_step1 {G : Type*} [Group G] {a b : G}
    (hcomm : a * b = b * a) :
    ∀ g h : closure {x | x = a ∨ x = b},
      ∃ i j k l : ℤ, (g : G) = a ^ i * b ^ j ∧ (h : G) = a ^ k * b ^ l := by
  have hab : Commute a b := hcomm
  -- Every single element of the subgroup can be written as `a ^ i * b ^ j`.
  have key : ∀ x, x ∈ closure {x | x = a ∨ x = b} → ∃ i j : ℤ, x = a ^ i * b ^ j := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem w hw =>
        rcases hw with hw | hw
        · exact ⟨1, 0, by rw [hw, zpow_one, zpow_zero, mul_one]⟩
        · exact ⟨0, 1, by rw [hw, zpow_one, zpow_zero, one_mul]⟩
    | one => exact ⟨0, 0, by rw [zpow_zero, zpow_zero, mul_one]⟩
    | mul p q _ _ ihp ihq =>
        obtain ⟨i, j, hp⟩ := ihp
        obtain ⟨k, l, hq⟩ := ihq
        refine ⟨i + k, j + l, ?_⟩
        rw [hp, hq, zpow_add, zpow_add]
        -- move `b ^ j` past `a ^ k` using commutativity of the powers
        have hc : b ^ j * a ^ k = a ^ k * b ^ j := (hab.symm.zpow_zpow j k)
        rw [mul_assoc, ← mul_assoc (b ^ j), hc]
        group
    | inv p _ ihp =>
        obtain ⟨i, j, hp⟩ := ihp
        refine ⟨-i, -j, ?_⟩
        rw [hp, mul_inv_rev, zpow_neg, zpow_neg]
        -- `(b ^ j)⁻¹ * (a ^ i)⁻¹ = (a ^ i)⁻¹ * (b ^ j)⁻¹`
        have hc : (b ^ j)⁻¹ * (a ^ i)⁻¹ = (a ^ i)⁻¹ * (b ^ j)⁻¹ :=
          (hab.symm.zpow_zpow j i).inv_inv
        exact hc
  -- Apply the single-element normal form to both `g` and `h`.
  rintro ⟨g, hg⟩ ⟨h, hh⟩
  obtain ⟨i, j, hij⟩ := key g hg
  obtain ⟨k, l, hkl⟩ := key h hh
  exact ⟨i, j, k, l, hij, hkl⟩
