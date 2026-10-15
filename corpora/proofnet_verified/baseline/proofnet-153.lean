import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators InnerProductSpace

set_option maxHeartbeats 400000

/-Informal Statement

Suppose $k \geq 3, x, y \in \mathbb{R}^k, |x - y| = d > 0$, and $r > 0$. Prove that if $2r > d$, there are infinitely many $z \in \mathbb{R}^k$ such that $|z-x|=|z-y|=r$.
-/

/-Informal Proof

(a) Let w be any vector satisfying the following two equations:
$$
\begin{aligned}
\mathbf{w} \cdot(\mathbf{x}-\mathbf{y}) &=0, \\
|\mathbf{w}|^2 &=r^2-\frac{d^2}{4} .
\end{aligned}
$$
From linear algebra it is known that all but one of the components of a solution $\mathbf{w}$ of the first equation can be arbitrary. The remaining component is then uniquely determined. Also, if $w$ is any non-zero solution of the first equation, there is a unique positive number $t$ such that $t$ w satisfies both equations. (For example, if $x_1 \neq y_1$, the first equation is satisfied whenever
$$
z_1=\frac{z_2\left(x_2-y_2\right)+\cdots+z_k\left(x_k-y_k\right)}{y_1-x_1} .
$$
If $\left(z_1, z_2, \ldots, z_k\right)$ satisfies this equation, so does $\left(t z_1, t z_2, \ldots, t z_k\right)$ for any real number $t$.) Since at least two of these components can vary independently, we can find a solution with these components having any prescribed ratio. This ratio does not change when we multiply by the positive number $t$ to obtain a solution of both equations. Since there are infinitely many ratios, there are infinitely many distinct solutions. For each such solution $\mathbf{w}$ the vector $\mathbf{z}=$ $\frac{1}{2} \mathrm{x}+\frac{1}{2} \mathrm{y}+\mathrm{w}$ is a solution of the required equation. For
$$
\begin{aligned}
|\mathrm{z}-\mathbf{x}|^2 &=\left|\frac{\mathbf{y}-\mathbf{x}}{2}+\mathbf{w}\right|^2 \\
&=\left|\frac{\mathbf{y}-\mathbf{x}}{2}\right|^2+2 \mathbf{w} \cdot \frac{\mathbf{x}-\mathbf{y}}{2}+|\mathbf{w}|^2 \\
&=\frac{d^2}{4}+0+r^2-\frac{d^2}{4} \\
&=r^2
\end{aligned}
$$
and a similar relation holds for $|z-y|^2$.
-/

theorem Rudin_exercise_1_16a
  (n : ℕ)
  (d r : ℝ)
  (x y _z : EuclideanSpace ℝ (Fin n)) -- R^n
  (h₁ : n ≥ 3)
  (h₂ : ‖x - y‖ = d)
  (h₃ : d > 0)
  (h₄ : r > 0)
  (h₅ : 2 * r > d)
  : Set.Infinite {z : EuclideanSpace ℝ (Fin n) | ‖z - x‖ = r ∧ ‖z - y‖ = r} := by
  /-
  ================================================================================
  PROOF OVERVIEW
  ================================================================================
  We need to show there are infinitely many points z in R^n such that
  ‖z - x‖ = r and ‖z - y‖ = r.

  Key observations:
  1. Such points lie on the intersection of two spheres centered at x and y, both with radius r.
  2. Points equidistant from x and y lie on the perpendicular bisector hyperplane H of segment [x,y].
  3. The intersection of the two spheres is a (n-2)-dimensional sphere in this hyperplane.
  4. For n ≥ 3, this intersection has dimension ≥ 1, hence infinitely many points.
  5. The condition 2r > d ensures r² - d²/4 > 0, so the intersection sphere has positive radius.

  Our construction:
  - Let m = (x + y)/2 be the midpoint
  - Let ρ = √(r² - d²/4) > 0 (the radius of the intersection sphere)
  - For any unit vector w perpendicular to (x - y), the point z = m + ρw satisfies both conditions
  - Since n ≥ 3, there are infinitely many such unit vectors w
  ================================================================================
  -/

  -- Step 1: Setup classical logic
  classical

  -- Step 2: Define key quantities
  -- Step 2.1: The midpoint of x and y
  let m : EuclideanSpace ℝ (Fin n) := (1/2 : ℝ) • x + (1/2 : ℝ) • y

  -- Step 2.2: The squared radius of the intersection sphere: ρ² = r² - d²/4
  -- First prove this is positive using h₅: 2r > d
  have hρ_sq_pos : r^2 - d^2/4 > 0 := by
    -- Step 2.2.1: From 2r > d, we get 4r² > d², so r² > d²/4
    have h : 2 * r > d := h₅
    have h' : (2 * r)^2 > d^2 := by
      apply sq_lt_sq'
      · linarith
      · linarith
    have h'' : 4 * r^2 > d^2 := by ring_nf at h' ⊢; exact h'
    linarith

  -- Step 2.3: Define ρ = √(r² - d²/4)
  let ρ : ℝ := Real.sqrt (r^2 - d^2/4)
  have hρ_pos : ρ > 0 := Real.sqrt_pos.mpr hρ_sq_pos

  -- Step 3: Define the orthogonal subspace to (x - y)
  -- This is the set of all vectors w such that ⟪w, x - y⟫ = 0
  let W : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
    (Submodule.span ℝ {x - y})ᗮ

  -- Step 3.1: Prove that W has dimension n - 1 (at least 2 when n ≥ 3)
  -- First, we need that x - y ≠ 0
  have hxy_ne : x - y ≠ 0 := by
    intro heq
    have : ‖x - y‖ = 0 := by simp [heq]
    rw [h₂] at this
    linarith

  -- Step 3.2: The dimension of span {x - y} is 1
  have h_dim_span : Module.finrank ℝ (Submodule.span ℝ {x - y}) = 1 := by
    rw [finrank_span_singleton hxy_ne]

  -- Step 3.3: The dimension of W is n - 1
  have h_dim_W : Module.finrank ℝ W = n - 1 := by
    have h_total : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n :=
      finrank_euclideanSpace_fin
    have h_orth : Module.finrank ℝ (Submodule.span ℝ {x - y}) + Module.finrank ℝ W =
                  Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) :=
      Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ {x - y})
    rw [h_dim_span, h_total] at h_orth
    omega

  -- Step 3.4: Since n ≥ 3, W has dimension at least 2
  have h_dim_W_ge_2 : Module.finrank ℝ W ≥ 2 := by
    rw [h_dim_W]
    omega

  -- Step 4: Define the construction function
  -- For each w ∈ W with ‖w‖ = 1, define f(w) = m + ρ • w
  -- This gives a point equidistant from x and y with the right distance

  -- Step 4.1: Define the unit sphere in W
  let S_W : Set W := {w : W | ‖(w : EuclideanSpace ℝ (Fin n))‖ = 1}

  -- Step 4.2: W has an inner product structure inherited from the ambient space
  -- (W inherits the inner product from EuclideanSpace via Submodule.innerProductSpace)
  -- We use letI to establish these instances for the remainder of the proof
  letI : InnerProductSpace ℝ W := Submodule.innerProductSpace W

  -- Step 4.2b: W is finite dimensional (as a submodule of a finite-dimensional space)
  -- EuclideanSpace ℝ (Fin n) is finite dimensional, so any submodule is also finite dimensional
  haveI : FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)) := inferInstance
  haveI : FiniteDimensional ℝ W := inferInstance

  -- Step 4.3: The unit sphere in W is infinite when dim W ≥ 2

  -- Step 4.3.0: Set up helpers before proving infiniteness
  -- Get indices for two basis vectors
  have h1_lt : (1 : ℕ) < Module.finrank ℝ W := by omega
  let i₀ : Fin (Module.finrank ℝ W) := ⟨0, by omega⟩
  let i₁ : Fin (Module.finrank ℝ W) := ⟨1, h1_lt⟩
  -- Get the standard orthonormal basis
  -- W has InnerProductSpace and FiniteDimensional instances via the inner product space structure
  let b : OrthonormalBasis (Fin (Module.finrank ℝ W)) ℝ W := stdOrthonormalBasis ℝ W
  let e₁ : W := b i₀
  let e₂ : W := b i₁

  have hS_W_infinite : Set.Infinite S_W := by
    -- Since dim W ≥ 2, the unit sphere in W has infinitely many points
    -- This is because W is a real vector space of dimension ≥ 2
    have h_nontrivial : Nontrivial W := by
      rw [← Module.finrank_pos_iff (R := ℝ)]
      have := h_dim_W_ge_2
      omega

    have h_ge : Module.finrank ℝ W ≥ 2 := h_dim_W_ge_2

    -- Step 4.3.2: e₁ and e₂ are orthonormal
    -- In Mathlib, b.orthonormal is (∀ i, ‖b i‖ = 1) ∧ (Pairwise fun i j => inner (b i) (b j) = 0)
    have horth := b.orthonormal
    have he₁_norm : ‖e₁‖ = 1 := horth.1 i₀
    have he₂_norm : ‖e₂‖ = 1 := horth.1 i₁
    have he₁e₂_orth : ⟪e₁, e₂⟫_ℝ = 0 := by
      have hne : i₀ ≠ i₁ := by simp [i₀, i₁]
      exact horth.2 hne

    -- Step 4.3.3: Define g : ℝ → W by g(θ) = cos θ • e₁ + sin θ • e₂
    let g : ℝ → W := fun θ => Real.cos θ • e₁ + Real.sin θ • e₂

    -- Step 4.3.4: Each g(θ) has norm 1
    have hg_norm : ∀ θ, ‖g θ‖ = 1 := by
      intro θ
      have hsq : ‖g θ‖^2 = 1 := by
        -- Expand the norm squared as inner product
        have he₁_inner : ⟪e₁, e₁⟫_ℝ = 1 := by
          rw [real_inner_self_eq_norm_sq, he₁_norm]; ring
        have he₂_inner : ⟪e₂, e₂⟫_ℝ = 1 := by
          rw [real_inner_self_eq_norm_sq, he₂_norm]; ring
        have he₂e₁_orth : ⟪e₂, e₁⟫_ℝ = 0 := by rw [real_inner_comm]; exact he₁e₂_orth
        -- Use the orthonormality to compute the norm
        -- First simplify individual inner product terms
        have hterm1 : ⟪Real.cos θ • e₁, Real.cos θ • e₁⟫_ℝ = Real.cos θ ^ 2 := by
          rw [inner_smul_left, inner_smul_right, he₁_inner]
          simp only [RCLike.conj_to_real]
          ring
        have hterm2 : ⟪Real.cos θ • e₁, Real.sin θ • e₂⟫_ℝ = 0 := by
          rw [inner_smul_left, inner_smul_right, he₁e₂_orth]
          simp only [RCLike.conj_to_real]
          ring
        have hterm3 : ⟪Real.sin θ • e₂, Real.cos θ • e₁⟫_ℝ = 0 := by
          rw [inner_smul_left, inner_smul_right, he₂e₁_orth]
          simp only [RCLike.conj_to_real]
          ring
        have hterm4 : ⟪Real.sin θ • e₂, Real.sin θ • e₂⟫_ℝ = Real.sin θ ^ 2 := by
          rw [inner_smul_left, inner_smul_right, he₂_inner]
          simp only [RCLike.conj_to_real]
          ring
        calc ‖g θ‖^2
            = ⟪g θ, g θ⟫_ℝ := by rw [real_inner_self_eq_norm_sq]
          _ = ⟪Real.cos θ • e₁ + Real.sin θ • e₂, Real.cos θ • e₁ + Real.sin θ • e₂⟫_ℝ := rfl
          _ = ⟪Real.cos θ • e₁, Real.cos θ • e₁ + Real.sin θ • e₂⟫_ℝ +
              ⟪Real.sin θ • e₂, Real.cos θ • e₁ + Real.sin θ • e₂⟫_ℝ := by
            rw [inner_add_left]
          _ = ⟪Real.cos θ • e₁, Real.cos θ • e₁⟫_ℝ +
              ⟪Real.cos θ • e₁, Real.sin θ • e₂⟫_ℝ +
              ⟪Real.sin θ • e₂, Real.cos θ • e₁⟫_ℝ +
              ⟪Real.sin θ • e₂, Real.sin θ • e₂⟫_ℝ := by
            rw [inner_add_right, inner_add_right]; ring
          _ = Real.cos θ ^ 2 + 0 + 0 + Real.sin θ ^ 2 := by
            rw [hterm1, hterm2, hterm3, hterm4]
          _ = 1 := by ring_nf; exact Real.cos_sq_add_sin_sq θ
      have hnorm_nonneg : ‖g θ‖ ≥ 0 := norm_nonneg _
      nlinarith [sq_nonneg (‖g θ‖)]

    -- Step 4.3.5: g maps to S_W
    have hg_mem : ∀ θ, g θ ∈ S_W := by
      intro θ
      simp only [S_W, Set.mem_setOf_eq]
      -- The norm of the coercion equals the norm in W
      exact hg_norm θ

    -- Step 4.3.6: g restricted to [0, π) is injective
    have hg_inj_on : Set.InjOn g (Set.Ico (0 : ℝ) Real.pi) := by
      intro θ₁ hθ₁ θ₂ hθ₂ heq
      -- From g(θ₁) = g(θ₂), we get cos θ₁ = cos θ₂ and sin θ₁ = sin θ₂
      have heq' : Real.cos θ₁ • e₁ + Real.sin θ₁ • e₂ = Real.cos θ₂ • e₁ + Real.sin θ₂ • e₂ := heq
      -- Compute inner products with e₁
      have he₁_inner : ⟪e₁, e₁⟫_ℝ = 1 := by
        rw [real_inner_self_eq_norm_sq, he₁_norm]; ring
      have he₂e₁ : ⟪e₂, e₁⟫_ℝ = 0 := by rw [real_inner_comm]; exact he₁e₂_orth
      -- Apply inner product with e₁ to both sides
      have hcos : Real.cos θ₁ = Real.cos θ₂ := by
        have h1 : ⟪Real.cos θ₁ • e₁ + Real.sin θ₁ • e₂, e₁⟫_ℝ =
                  ⟪Real.cos θ₂ • e₁ + Real.sin θ₂ • e₂, e₁⟫_ℝ := by rw [heq']
        -- Simplify using inner_add_left and inner_smul_left
        simp only [inner_add_left, inner_smul_left, he₁_inner, he₂e₁] at h1
        simp at h1
        exact h1
      -- On [0, π), cos determines θ uniquely
      have hθ₁_range : θ₁ ∈ Set.Ico (0 : ℝ) Real.pi := hθ₁
      have hθ₂_range : θ₂ ∈ Set.Ico (0 : ℝ) Real.pi := hθ₂
      -- Use that on [0, π], θ = arccos(cos θ)
      have h1 : θ₁ = Real.arccos (Real.cos θ₁) :=
        (Real.arccos_cos hθ₁_range.1 (le_of_lt hθ₁_range.2)).symm
      have h2 : θ₂ = Real.arccos (Real.cos θ₂) :=
        (Real.arccos_cos hθ₂_range.1 (le_of_lt hθ₂_range.2)).symm
      rw [h1, h2, hcos]

    -- Step 4.3.7: Set.Ico 0 π is infinite
    have hIco_infinite : Set.Infinite (Set.Ico (0 : ℝ) Real.pi) :=
      Set.infinite_coe_iff.mp (Set.Ico.infinite Real.pi_pos)

    -- Step 4.3.8: The image g(Ico 0 π) is infinite (injective image of infinite set)
    have hgImage_infinite : Set.Infinite (g '' (Set.Ico (0 : ℝ) Real.pi)) :=
      hIco_infinite.image hg_inj_on

    -- Step 4.3.9: This image is a subset of S_W
    have hgImage_subset : g '' (Set.Ico (0 : ℝ) Real.pi) ⊆ S_W := by
      intro w hw
      obtain ⟨θ, _, rfl⟩ := hw
      exact hg_mem θ

    -- Step 4.3.10: Conclude S_W is infinite
    exact Set.Infinite.mono hgImage_subset hgImage_infinite

  -- Step 5: Define the map from S_W to the target set
  let f : W → EuclideanSpace ℝ (Fin n) := fun w => m + ρ • (w : EuclideanSpace ℝ (Fin n))

  -- Step 5.1: Show f maps S_W into the target set
  have hf_maps : ∀ w ∈ S_W, f w ∈ {z : EuclideanSpace ℝ (Fin n) | ‖z - x‖ = r ∧ ‖z - y‖ = r} := by
    intro w hw
    simp only [S_W, Set.mem_setOf_eq] at hw
    simp only [Set.mem_setOf_eq]
    -- w is in W, so ⟪w, x - y⟫ = 0
    have hw_orth : @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (w : EuclideanSpace ℝ (Fin n)) (x - y) = 0 := by
      have hmem : x - y ∈ Submodule.span ℝ {x - y} := Submodule.mem_span_singleton_self (x - y)
      -- W = (span {x - y})ᗮ, so w ∈ W means w ⊥ (x - y)
      have hw_mem : (w : EuclideanSpace ℝ (Fin n)) ∈ W := w.property
      rw [Submodule.mem_orthogonal] at hw_mem
      rw [real_inner_comm]
      exact hw_mem (x - y) hmem

    -- Step 5.1.1: Compute ‖f w - x‖²
    have hfx : ‖f w - x‖^2 = r^2 := by
      -- f w - x = m + ρ • w - x = (1/2 x + 1/2 y) + ρ w - x
      --         = 1/2 y - 1/2 x + ρ w = -(1/2)(x - y) + ρ w
      have heq : f w - x = -(1/2 : ℝ) • (x - y) + ρ • (w : EuclideanSpace ℝ (Fin n)) := by
        simp only [f, m]
        simp only [sub_eq_add_neg]
        -- (1/2) • x + (1/2) • y + ρ • w - x = -(1/2) • (x - y) + ρ • w
        module
      rw [heq]
      -- ‖a + b‖² = ‖a‖² + 2⟪a, b⟫ + ‖b‖²
      have hw_orth' : @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (x - y) (w : EuclideanSpace ℝ (Fin n)) = 0 := by
        rw [real_inner_comm]; exact hw_orth
      calc ‖-(1/2 : ℝ) • (x - y) + ρ • (w : EuclideanSpace ℝ (Fin n))‖^2
          = ‖-(1/2 : ℝ) • (x - y)‖^2 +
            2 * @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (-(1/2 : ℝ) • (x - y)) (ρ • (w : EuclideanSpace ℝ (Fin n))) +
            ‖ρ • (w : EuclideanSpace ℝ (Fin n))‖^2 := by
              rw [norm_add_sq_real]
        _ = (1/2)^2 * ‖x - y‖^2 +
            2 * (-(1/2) * ρ * @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (x - y) (w : EuclideanSpace ℝ (Fin n))) +
            ρ^2 * ‖(w : EuclideanSpace ℝ (Fin n))‖^2 := by
              simp only [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (1:ℝ)/2 > 0),
                         abs_of_pos hρ_pos]
              rw [real_inner_smul_left, real_inner_smul_right]
              ring
        _ = (1/2)^2 * d^2 + 2 * (-(1/2) * ρ * 0) + ρ^2 * 1^2 := by
              rw [h₂, hw, hw_orth']
        _ = d^2/4 + ρ^2 := by ring
        _ = d^2/4 + (r^2 - d^2/4) := by
              congr 1
              rw [Real.sq_sqrt (le_of_lt hρ_sq_pos)]
        _ = r^2 := by ring

    -- Step 5.1.2: Compute ‖f w - y‖²
    have hfy : ‖f w - y‖^2 = r^2 := by
      -- f w - y = m + ρ • w - y = (1/2 x + 1/2 y) + ρ w - y
      --         = 1/2 x - 1/2 y + ρ w = (1/2)(x - y) + ρ w
      have heq : f w - y = (1/2 : ℝ) • (x - y) + ρ • (w : EuclideanSpace ℝ (Fin n)) := by
        simp only [f, m]
        simp only [sub_eq_add_neg]
        module
      rw [heq]
      have hw_orth' : @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (x - y) (w : EuclideanSpace ℝ (Fin n)) = 0 := by
        rw [real_inner_comm]; exact hw_orth
      calc ‖(1/2 : ℝ) • (x - y) + ρ • (w : EuclideanSpace ℝ (Fin n))‖^2
          = ‖(1/2 : ℝ) • (x - y)‖^2 +
            2 * @inner ℝ (EuclideanSpace ℝ (Fin n)) _ ((1/2 : ℝ) • (x - y)) (ρ • (w : EuclideanSpace ℝ (Fin n))) +
            ‖ρ • (w : EuclideanSpace ℝ (Fin n))‖^2 := by
              rw [norm_add_sq_real]
        _ = (1/2)^2 * ‖x - y‖^2 +
            2 * ((1/2) * ρ * @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (x - y) (w : EuclideanSpace ℝ (Fin n))) +
            ρ^2 * ‖(w : EuclideanSpace ℝ (Fin n))‖^2 := by
              simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (1:ℝ)/2 > 0),
                         abs_of_pos hρ_pos]
              rw [real_inner_smul_left, real_inner_smul_right]
              ring
        _ = (1/2)^2 * d^2 + 2 * ((1/2) * ρ * 0) + ρ^2 * 1^2 := by
              rw [h₂, hw, hw_orth']
        _ = d^2/4 + ρ^2 := by ring
        _ = d^2/4 + (r^2 - d^2/4) := by
              congr 1
              rw [Real.sq_sqrt (le_of_lt hρ_sq_pos)]
        _ = r^2 := by ring

    -- Step 5.1.3: Take square roots
    constructor
    · have hr_nonneg : r ≥ 0 := le_of_lt h₄
      have hnorm_nonneg : ‖f w - x‖ ≥ 0 := norm_nonneg _
      nlinarith [sq_nonneg (‖f w - x‖ - r), hfx]
    · have hr_nonneg : r ≥ 0 := le_of_lt h₄
      have hnorm_nonneg : ‖f w - y‖ ≥ 0 := norm_nonneg _
      nlinarith [sq_nonneg (‖f w - y‖ - r), hfy]

  -- Step 5.2: Show f is injective on S_W
  have hf_inj : Set.InjOn f S_W := by
    intro w₁ hw₁ w₂ hw₂ heq
    simp only [f] at heq
    -- m + ρ • w₁ = m + ρ • w₂  =>  ρ • w₁ = ρ • w₂  =>  w₁ = w₂ (since ρ > 0)
    have h1 : ρ • (w₁ : EuclideanSpace ℝ (Fin n)) = ρ • (w₂ : EuclideanSpace ℝ (Fin n)) := by
      have := add_left_cancel heq
      exact this
    have h2 : (w₁ : EuclideanSpace ℝ (Fin n)) = (w₂ : EuclideanSpace ℝ (Fin n)) := by
      have hρ_ne : ρ ≠ 0 := ne_of_gt hρ_pos
      have := smul_right_injective (EuclideanSpace ℝ (Fin n)) hρ_ne
      exact this h1
    exact Subtype.ext h2

  -- Step 6: f(S_W) is infinite and contained in the target set
  have hImage_infinite : Set.Infinite (f '' S_W) :=
    hS_W_infinite.image hf_inj

  have hImage_subset : f '' S_W ⊆ {z : EuclideanSpace ℝ (Fin n) | ‖z - x‖ = r ∧ ‖z - y‖ = r} := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact hf_maps w hw

  -- Step 7: Conclude
  exact Set.Infinite.mono hImage_subset hImage_infinite
