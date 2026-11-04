theorem helper_kernel_support_step1 {I J : Type*} {x : J → ℝ} {y : I → ℝ} {j : J} {s : I}
    (h : x j * y s ≠ 0) : x j * y s ≠ 0 := h

theorem helper_kernel_support_step2 {I J : Type*} [DecidableEq I] [DecidableEq J]
    {T : Set (I × J)} {D Dτ : Matrix I J ℝ} {τ : ℝ} {s : I} {j : J}
    (hDτ : Dτ = D + τ • Matrix.single s j (1 : ℝ))
    (hD : ∀ s' j', (s', j') ∉ T → D s' j' = 0) (hsj : (s, j) ∈ T) :
    ∀ s' j', (s', j') ∉ T → Dτ s' j' = 0 := by
  intro s' j' hnot
  have hne : ¬ (s = s' ∧ j = j') := by
    rintro ⟨rfl, rfl⟩
    exact hnot hsj
  rw [hDτ]
  simp [Matrix.single_apply_of_ne s j τ s' j' hne, hD s' j' hnot]

theorem helper_kernel_support_step3 {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] {D Dτ : Matrix I J ℝ} {τ : ℝ} {s : I} {j : J} {x : J → ℝ}
    (hDτ : Dτ = D + τ • Matrix.single s j (1 : ℝ))
    (hx : D.mulVec x = 0) :
    Dτ.mulVec x = (τ * x j) • (Pi.single s (1 : ℝ) : I → ℝ) := by
  rw [hDτ, Matrix.add_mulVec, hx, zero_add, Matrix.smul_mulVec, Matrix.single_mulVec]
  ext i
  simp [Pi.single_apply, Function.update_apply]

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

theorem helper_kernel_support_step6 {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    {D Dτ : Matrix I J ℝ}
    {τ : ℝ} {s : I} {j : J}
    (step5 : ∀ w : J → ℝ,
        (D.mulVec w = Dτ.mulVec w - (τ * w j) • (Pi.single s (1 : ℝ) : I → ℝ)) ∧
          D.mulVec w ∈ LinearMap.range Dτ.mulVecLin) :
    LinearMap.range D.mulVecLin ≤ LinearMap.range Dτ.mulVecLin := by
  rintro z ⟨w, rfl⟩
  exact (step5 w).2

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

theorem helper_kernel_support_step8 {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    {D Dτ : Matrix I J ℝ} {s : I}
    (step4 : (Pi.single s (1 : ℝ) : I → ℝ) ∈ LinearMap.range Dτ.mulVecLin)
    (step6 : LinearMap.range D.mulVecLin ≤ LinearMap.range Dτ.mulVecLin)
    (step7 : (Pi.single s (1 : ℝ) : I → ℝ) ∉ LinearMap.range D.mulVecLin) :
    Dτ.rank > D.rank := by
  have hlt : LinearMap.range D.mulVecLin < LinearMap.range Dτ.mulVecLin :=
    lt_iff_le_not_ge.mpr ⟨step6, fun hge => step7 (hge step4)⟩
  exact Submodule.finrank_lt_finrank_of_lt hlt

theorem helper_kernel_support_step9 {I J : Type*} [Fintype I] [Fintype J] {T : Set (I × J)}
    {D Dτ : Matrix I J ℝ}
    (hmax : ∀ A : Matrix I J ℝ, (∀ s j, (s, j) ∉ T → A s j = 0) → A.rank ≤ D.rank)
    (step2 : ∀ s j, (s, j) ∉ T → Dτ s j = 0) (step8 : Dτ.rank > D.rank) : False :=
  absurd (hmax Dτ step2) (not_le.mpr step8)

variable {I J : Type*} [Fintype I] [Fintype J]

def SupportedOn (T : Set (I × J)) (D : Matrix I J ℝ) : Prop :=
  ∀ s j, (s, j) ∉ T → D s j = 0

theorem kernel_support {T : Set (I × J)} {D : Matrix I J ℝ}
  (hD : SupportedOn T D)
  (hmax : ∀ A : Matrix I J ℝ, SupportedOn T A → A.rank ≤ D.rank)
  {x : J → ℝ} {y : I → ℝ}
  (hx : x ∈ LinearMap.ker D.mulVecLin)
  (hy : y ∈ LinearMap.ker Dᵀ.mulVecLin)
  {s : I} {j : J} (hsj : (s, j) ∈ T) :
  x j * y s = 0 := by
  classical
  

  have habsurd1 : ¬(x j * y s ≠ 0) := by
    intro hsuppose1
    have step1 : x j * y s ≠ 0 := by
        exact helper_kernel_support_step1 hsuppose1

    obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ ≠ 0 := ⟨1, one_ne_zero⟩
    set Dτ : Matrix I J ℝ := D + τ • Matrix.single s j (1 : ℝ) with hDτ
    have step2 : SupportedOn T Dτ := by
        exact helper_kernel_support_step2 hDτ hD hsj

    have step3 : Dτ.mulVec x = (τ * x j) • (Pi.single s (1 : ℝ) : I → ℝ) := by
        exact helper_kernel_support_step3 hDτ (by simpa using LinearMap.mem_ker.mp hx)

    have step4 : (Pi.single s (1 : ℝ) : I → ℝ) ∈ LinearMap.range Dτ.mulVecLin := by
        exact helper_kernel_support_step4 hτ step3 hsuppose1

    have step5 : ∀ w : J → ℝ,
          (D.mulVec w = Dτ.mulVec w - (τ * w j) • (Pi.single s (1 : ℝ) : I → ℝ)) ∧
            D.mulVec w ∈ LinearMap.range Dτ.mulVecLin := by
        exact helper_kernel_support_step5 hDτ step4

    have step6 : LinearMap.range D.mulVecLin ≤ LinearMap.range Dτ.mulVecLin := by
        exact helper_kernel_support_step6 step5

    have hyann : ∀ v ∈ LinearMap.range D.mulVecLin, y ⬝ᵥ v = 0 := by
        rintro v ⟨w, rfl⟩
        have hy' : Dᵀ.mulVec y = 0 := LinearMap.mem_ker.mp hy
        have key := Matrix.dotProduct_transpose_mulVec D w y
        rw [hy', dotProduct_zero] at key
        exact key.symm
    have hys : y s ≠ 0 := by
        intro h
        exact hsuppose1 (by rw [h, mul_zero])
    have step7 : (Pi.single s (1 : ℝ) : I → ℝ) ∉ LinearMap.range D.mulVecLin := by
        exact helper_kernel_support_step7 hyann hys

    have step8 : Dτ.rank > D.rank := by
        exact helper_kernel_support_step8 step4 step6 step7

    have step9 : False := by
        exact helper_kernel_support_step9 hmax step2 step8
    exact step9

  exact not_not.mp habsurd1