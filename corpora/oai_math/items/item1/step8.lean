import Mathlib
import Pistis

open Matrix

theorem helper_kernel_support_step8 {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    {D Dτ : Matrix I J ℝ} {s : I}
    (step4 : (Pi.single s (1 : ℝ) : I → ℝ) ∈ LinearMap.range Dτ.mulVecLin)
    (step6 : LinearMap.range D.mulVecLin ≤ LinearMap.range Dτ.mulVecLin)
    (step7 : (Pi.single s (1 : ℝ) : I → ℝ) ∉ LinearMap.range D.mulVecLin) :
    Dτ.rank > D.rank := by
  have hlt : LinearMap.range D.mulVecLin < LinearMap.range Dτ.mulVecLin :=
    lt_iff_le_not_ge.mpr ⟨step6, fun hge => step7 (hge step4)⟩
  exact Submodule.finrank_lt_finrank_of_lt hlt
