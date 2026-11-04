import Mathlib
import Pistis

open Matrix

theorem helper_kernel_support_step7 {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    {D : Matrix I J ℝ}
    {s : I} {y : I → ℝ}
    (hyann : ∀ v ∈ LinearMap.range D.mulVecLin, y ⬝ᵥ v = 0) (hys : y s ≠ 0) :
    (Pi.single s (1 : ℝ) : I → ℝ) ∉ LinearMap.range D.mulVecLin := by
  rintro ⟨w, hw⟩
  have h0 := hyann (D.mulVecLin w) ⟨w, rfl⟩
  rw [hw] at h0
  apply hys
  simpa [dotProduct, Pi.single_apply] using h0
