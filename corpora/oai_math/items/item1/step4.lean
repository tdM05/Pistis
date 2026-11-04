import Mathlib
import Pistis

open Matrix

theorem helper_kernel_support_step4 {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    {Dτ : Matrix I J ℝ} {τ : ℝ} (hτ : τ ≠ 0) {s : I} {j : J} {x : J → ℝ} {y : I → ℝ}
    (hstep3 : Dτ.mulVec x = (τ * x j) • (Pi.single s (1 : ℝ) : I → ℝ))
    (hxy : x j * y s ≠ 0) :
    (Pi.single s (1 : ℝ) : I → ℝ) ∈ LinearMap.range Dτ.mulVecLin := by
  have hxj : x j ≠ 0 := fun h => hxy (by rw [h, zero_mul])
  have hc : τ * x j ≠ 0 := mul_ne_zero hτ hxj
  have hmem : (τ * x j) • (Pi.single s (1 : ℝ) : I → ℝ) ∈ LinearMap.range Dτ.mulVecLin :=
    ⟨x, hstep3⟩
  have hs := (LinearMap.range Dτ.mulVecLin).smul_mem (τ * x j)⁻¹ hmem
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at hs
  exact hs
