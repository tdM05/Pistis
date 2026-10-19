have hDw : ∀ w : J → ℝ,
      D.mulVec w = Dτ.mulVec w - (τ * w j) • (Pi.single s (1 : ℝ) : I → ℝ) ∧
        D.mulVec w ∈ LinearMap.range Dτ.mulVecLin := by sorry