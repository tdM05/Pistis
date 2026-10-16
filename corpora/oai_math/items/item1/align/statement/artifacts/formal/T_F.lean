import Mathlib
open Matrix
variable {I J : Type*} [Fintype I] [Fintype J]
def SupportedOn (T : Set (I × J)) (D : Matrix I J ℝ) : Prop := ∀ s j, (s, j) ∉ T → D s j = 0
theorem kernel_support {T : Set (I × J)} {D : Matrix I J ℝ} (hD : SupportedOn T D) (hmax : ∀ A : Matrix I J ℝ, SupportedOn T A → A.rank ≤ D.rank) {x : J → ℝ} {y : I → ℝ} (hx : x ∈ LinearMap.ker D.mulVecLin) (hy : y ∈ LinearMap.ker Dᵀ.mulVecLin) {s : I} {j : J} (hsj : (s, j) ∈ T) : x j * y s = 0 := by sorry
