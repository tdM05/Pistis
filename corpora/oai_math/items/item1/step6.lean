import Mathlib
import Pistis

open Matrix

theorem helper_kernel_support_step6 {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    {D Dτ : Matrix I J ℝ}
    {τ : ℝ} {s : I} {j : J}
    (step5 : ∀ w : J → ℝ,
        (D.mulVec w = Dτ.mulVec w - (τ * w j) • (Pi.single s (1 : ℝ) : I → ℝ)) ∧
          D.mulVec w ∈ LinearMap.range Dτ.mulVecLin) :
    LinearMap.range D.mulVecLin ≤ LinearMap.range Dτ.mulVecLin := by
  rintro z ⟨w, rfl⟩
  exact (step5 w).2
