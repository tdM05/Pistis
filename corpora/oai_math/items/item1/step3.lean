import Mathlib
import Pistis

open Matrix

theorem helper_kernel_support_step3 {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] {D Dτ : Matrix I J ℝ} {τ : ℝ} {s : I} {j : J} {x : J → ℝ}
    (hDτ : Dτ = D + τ • Matrix.single s j (1 : ℝ))
    (hx : D.mulVec x = 0) :
    Dτ.mulVec x = (τ * x j) • (Pi.single s (1 : ℝ) : I → ℝ) := by
  rw [hDτ, Matrix.add_mulVec, hx, zero_add, Matrix.smul_mulVec, Matrix.single_mulVec]
  ext i
  simp [Pi.single_apply, Function.update_apply]
