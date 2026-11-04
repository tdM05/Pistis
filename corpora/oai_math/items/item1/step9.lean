import Mathlib
import Pistis

open Matrix

theorem helper_kernel_support_step9 {I J : Type*} [Fintype I] [Fintype J] {T : Set (I × J)}
    {D Dτ : Matrix I J ℝ}
    (hmax : ∀ A : Matrix I J ℝ, (∀ s j, (s, j) ∉ T → A s j = 0) → A.rank ≤ D.rank)
    (step2 : ∀ s j, (s, j) ∉ T → Dτ s j = 0) (step8 : Dτ.rank > D.rank) : False :=
  absurd (hmax Dτ step2) (not_le.mpr step8)
