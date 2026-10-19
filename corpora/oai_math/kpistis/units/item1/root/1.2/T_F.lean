obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ ≠ 0 := ⟨1, one_ne_zero⟩
  set Dτ : Matrix I J ℝ := D + τ • Matrix.single s j (1 : ℝ) with hDτ
  have hsupp : SupportedOn T Dτ := by sorry