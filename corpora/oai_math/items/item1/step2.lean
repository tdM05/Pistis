import Mathlib
import Pistis

open Matrix

theorem helper_kernel_support_step2 {I J : Type*} [DecidableEq I] [DecidableEq J]
    {T : Set (I × J)} {D Dτ : Matrix I J ℝ} {τ : ℝ} {s : I} {j : J}
    (hDτ : Dτ = D + τ • Matrix.single s j (1 : ℝ))
    (hD : ∀ s' j', (s', j') ∉ T → D s' j' = 0) (hsj : (s, j) ∈ T) :
    ∀ s' j', (s', j') ∉ T → Dτ s' j' = 0 := by
  intro s' j' hnot
  have hne : ¬ (s = s' ∧ j = j') := by
    rintro ⟨rfl, rfl⟩
    exact hnot hsj
  rw [hDτ]
  simp [Matrix.single_apply_of_ne s j τ s' j' hne, hD s' j' hnot]
