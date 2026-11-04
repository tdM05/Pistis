import Mathlib
import Pistis

open Matrix

theorem helper_kernel_support_step5 {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] {D Dτ : Matrix I J ℝ} {τ : ℝ} {s : I} {j : J}
    (hDτ : Dτ = D + τ • Matrix.single s j (1 : ℝ))
    (step4 : (Pi.single s (1 : ℝ) : I → ℝ) ∈ LinearMap.range Dτ.mulVecLin) :
    ∀ w : J → ℝ,
      (D.mulVec w = Dτ.mulVec w - (τ * w j) • (Pi.single s (1 : ℝ) : I → ℝ)) ∧
        D.mulVec w ∈ LinearMap.range Dτ.mulVecLin := by
  intro w
  have heq : D.mulVec w = Dτ.mulVec w - (τ * w j) • (Pi.single s (1 : ℝ) : I → ℝ) := by
    rw [hDτ, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.single_mulVec]
    ext i
    simp [Pi.single_apply, Function.update_apply]
  refine ⟨heq, ?_⟩
  rw [heq]
  exact (LinearMap.range Dτ.mulVecLin).sub_mem ⟨w, rfl⟩
    ((LinearMap.range Dτ.mulVecLin).smul_mem (τ * w j) step4)
