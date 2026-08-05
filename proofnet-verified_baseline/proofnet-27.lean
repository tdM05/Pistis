import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators



/-Informal Statement

Suppose $T \in \mathcal{L}(V)$ is self-adjoint, $\lambda \in \mathbf{F}$, and $\epsilon>0$. Prove that if there exists $v \in V$ such that $\|v\|=1$ and $\|T v-\lambda v\|<\epsilon,$ then $T$ has an eigenvalue $\lambda^{\prime}$ such that $\left|\lambda-\lambda^{\prime}\right|<\epsilon$.
-/

/-Informal Proof

Let $T \in \mathcal{L}(V)$ be a self-adjoint, and let $\lambda \in \mathbf{F}$ and $\epsilon>0$.
By the Spectral Theorem, there is $e_1, \ldots, e_n$ an orthonormal basis of $V$ consisting of eigenvectors of $T$ and let $\lambda_1, \ldots, \lambda_n$ denote their corresponding eigenvalues.
Choose an eigenvalue $\lambda^{\prime}$ of $T$ such that $\left|\lambda^{\prime}-\lambda\right|^2$ is minimized.
There are $a_1, \ldots, a_n \in \mathbb{F}$ such that
$$
v=a_1 e_1+\cdots+a_n e_n .
$$
Thus, we have
$$
\begin{aligned}
\epsilon^2 & >|| T v-\left.\lambda v\right|^2 \\
& =\left|\left\langle T v-\lambda v, e_1\right\rangle\right|^2+\cdots+\left|\left\langle T v-\lambda v, e_n\right\rangle\right|^2 \\
& =\left|\lambda_1 a_1-\lambda a_1\right|^2+\cdots+\left|\lambda_n a_n-\lambda a_n\right|^2 \\
& =\left|a_1\right|^2\left|\lambda_1-\lambda\right|^2+\cdots+\left|a_n\right|^2\left|\lambda_n-\lambda\right|^2 \\
& \geq\left|a_1\right|^2\left|\lambda^{\prime}-\lambda\right|^2+\cdots+\left|a_n\right|^2\left|\lambda^{\prime}-\lambda\right|^2 \\
& =\left|\lambda^{\prime}-\lambda\right|^2
\end{aligned}
$$
where the second and fifth lines follow from $6.30$ (the fifth because $\|v\|=1$ ). Now, we taking the square root.
Hence, $T$ has an eigenvalue $\lambda^{\prime}$ such that $\left|\lambda^{\prime}-\lambda\right|<\epsilon$
-/

theorem Axler_exercise_7_14 {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
  [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  {T : Module.End 𝕜 V} (hT : IsSelfAdjoint T)
  {l : 𝕜} {ε : ℝ} (he : ε > 0) : (∃ v : V, ‖v‖= 1 ∧ ‖T v - l • v‖ < ε) →
  (∃ l' : T.Eigenvalues, ‖l - l'‖ < ε) := by
  -- Step 1: introduce classical logic and destruct the approximate eigenvector data.
  classical
  intro hApprox
  -- Step 1.1: pick a unit vector `v` with the stated approximation property.
  rcases hApprox with ⟨v, hvnorm, hvapprox⟩
  -- Step 2: upgrade the self-adjoint assumption to the symmetric form given by the spectral theorem.
  have hSym : LinearMap.IsSymmetric T :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint T).mpr hT
  -- Step 2.1: choose the orthonormal eigenbasis and the corresponding eigenvalues.
  let n := Module.finrank 𝕜 V
  have hn : Module.finrank 𝕜 V = n := rfl
  let b := hSym.eigenvectorBasis hn
  let coords : Fin n → 𝕜 := b.repr v
  let lam : Fin n → 𝕜 := fun i => ((hSym.eigenvalues hn i : ℝ) : 𝕜)
  -- Step 3: record the coordinate formula for `T v` in the eigenbasis.
  have h_repr_mul :
      ∀ i : Fin n, (b.repr (T v)) i = lam i * coords i := by
    intro i
    -- Step 3.1: apply the diagonalization lemma and rewrite using current notation.
    simpa [b, coords, lam] using hSym.eigenvectorBasis_apply_self_apply hn v i
  -- Step 4: express the coordinates of the residual vector `T v - l • v`.
  have h_repr_res :
      ∀ i : Fin n, (b.repr (T v - l • v)) i = (lam i - l) * coords i := by
    intro i
    -- Step 4.1: expand linearity and collapse with Step 3.
    have hSub :
        (b.repr (T v - l • v)) i =
          (b.repr (T v)) i - (b.repr (l • v)) i := by
      simp [map_sub]
    have hS := h_repr_mul i
    have hSmul : (b.repr (l • v)) i = l * coords i := by
      simp [coords]
    -- Step 4.2: combine the two identities and factor common terms.
    rw [hSub, hS, hSmul]
    ring
  -- Step 5: turn the coordinate formula into an equality of squared norms.
  have h_coord_sq :
      ∀ i : Fin n, ‖(b.repr (T v - l • v)) i‖ ^ 2 =
        ‖lam i - l‖ ^ 2 * ‖coords i‖ ^ 2 := by
    intro i
    -- Step 5.1: compute the norm of the scalar product in the base field.
    rw [h_repr_res i, norm_mul, mul_pow]
  -- Step 6: identify the weighted sum of squares with `‖T v - l • v‖^2`.
  have h_sum_eq :
      ∑ i : Fin n, ‖lam i - l‖ ^ 2 * ‖coords i‖ ^ 2 = ‖T v - l • v‖ ^ 2 := by
    -- Step 6.1: rewrite each summand as the square of a scalar multiple.
    have h₁ :
        ∑ i : Fin n, ‖lam i - l‖ ^ 2 * ‖coords i‖ ^ 2 =
          ∑ i : Fin n, ‖(lam i - l) * coords i‖ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro i _
      simp [pow_two, norm_mul, mul_comm, mul_left_comm, mul_assoc]
    -- Step 6.2: replace each scalar multiple by the corresponding coordinate.
    have h₂ :
        ∑ i : Fin n, ‖(lam i - l) * coords i‖ ^ 2 =
          ∑ i : Fin n, ‖(b.repr (T v - l • v)) i‖ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [h_repr_res i]
    -- Step 6.3: express the remaining sum via the Euclidean norm.
    have h₃ :
        ∑ i : Fin n, ‖(b.repr (T v - l • v)) i‖ ^ 2 =
          ‖b.repr (T v - l • v)‖ ^ 2 := by
      simpa using (EuclideanSpace.norm_sq_eq (b.repr (T v - l • v))).symm
    -- Step 6.4: transfer the norm back to `V`.
    have h_isometry :=
      LinearIsometryEquiv.norm_map (b.repr) (T v - l • v)
    have h₄_norm : ‖b.repr (T v) - l • b.repr v‖ = ‖T v - l • v‖ := by
      simpa [map_sub] using h_isometry
    have h₄ :
        ‖b.repr (T v - l • v)‖ ^ 2 = ‖T v - l • v‖ ^ 2 := by
      simpa [h_isometry]
    -- Step 6.5: assemble the equalities.
    calc
      ∑ i : Fin n, ‖lam i - l‖ ^ 2 * ‖coords i‖ ^ 2
          = ∑ i, ‖(lam i - l) * coords i‖ ^ 2 := h₁
      _ = ∑ i, ‖(b.repr (T v - l • v)) i‖ ^ 2 := h₂
      _ = ‖b.repr (T v - l • v)‖ ^ 2 := h₃
      _ = ‖b.repr (T v) - l • b.repr v‖ ^ 2 := by
        simp [map_sub]
      _ = ‖T v - l • v‖ ^ 2 := by
        simp [h₄_norm]
  -- Step 7: note that the squared coordinates of `v` add up to `1`.
  have h_weight_sum : ∑ i : Fin n, ‖coords i‖ ^ 2 = 1 := by
    -- Step 7.1: rewrite the sum as the squared norm in the eigenbasis.
    have h_coords_sq :
        ∑ i : Fin n, ‖coords i‖ ^ 2 = ‖b.repr v‖ ^ 2 := by
      simpa [coords] using (EuclideanSpace.norm_sq_eq (b.repr v)).symm
    -- Step 7.2: translate the squared norm back to `V`.
    have h_isometry :=
      LinearIsometryEquiv.norm_map (b.repr) v
    have h_norm_sq : ‖b.repr v‖ ^ 2 = ‖v‖ ^ 2 := by
      simp [h_isometry]
    -- Step 7.3: use the unit-length condition on `v`.
    have h_unit : ‖v‖ ^ 2 = 1 := by simp [hvnorm]
    simp [h_coords_sq, h_unit]
  -- Step 8: deduce a strict upper bound on the weighted sum.
  have h_sum_lt : ∑ i : Fin n, ‖lam i - l‖ ^ 2 * ‖coords i‖ ^ 2 < ε ^ 2 := by
    -- Step 8.1: square the approximation inequality.
    have h_sq_lt : ‖T v - l • v‖ ^ 2 < ε ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg _) (le_of_lt he)).mpr hvapprox
    -- Step 8.2: translate via the identity from Step 6.
    simpa [h_sum_eq]
  -- Step 9: prove that some index realises a strict quadratic bound.
  have h_exists_sq :
      ∃ i : Fin n, ‖lam i - l‖ ^ 2 < ε ^ 2 := by
    classical
    -- Step 9.1: argue by contradiction using the non-negativity of the weights.
    by_contra hcontra
    -- Step 9.2: convert the negated existence into pointwise inequalities.
    have hforall' : ∀ i : Fin n, ε ^ 2 ≤ ‖lam i - l‖ ^ 2 := by
      intro i
      have hnot := (not_exists.mp hcontra) i
      exact not_lt.mp hnot
    -- Step 9.3: bound the weighted sum from below by `ε^2`.
    have h_sum_ge :
        ∑ i : Fin n, ε ^ 2 * ‖coords i‖ ^ 2 ≤
          ∑ i : Fin n, ‖lam i - l‖ ^ 2 * ‖coords i‖ ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro i _
      have h_nonneg : 0 ≤ ‖coords i‖ ^ 2 := sq_nonneg _
      have h_mul :=
        mul_le_mul_of_nonneg_right (hforall' i) h_nonneg
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using h_mul
    -- Step 9.4: evaluate the left-hand sum using Step 7.
    have h_left_sum :
        ∑ i : Fin n, ε ^ 2 * ‖coords i‖ ^ 2 = ε ^ 2 := by
      classical
      calc
        ∑ i : Fin n, ε ^ 2 * ‖coords i‖ ^ 2
            = ε ^ 2 * ∑ i, ‖coords i‖ ^ 2 := by
              simp [Finset.mul_sum]
        _ = ε ^ 2 * 1 := by simp [h_weight_sum]
        _ = ε ^ 2 := mul_one _
    -- Step 9.5: combine the bounds to contradict Step 8.
    have h_ge : ε ^ 2 ≤ ∑ i : Fin n, ‖lam i - l‖ ^ 2 * ‖coords i‖ ^ 2 := by
      simpa [h_left_sum] using h_sum_ge
    exact (not_le_of_gt h_sum_lt) h_ge
  -- Step 10: choose the index and drop the square to obtain the desired inequality.
  obtain ⟨i₀, hi₀⟩ := h_exists_sq
  have hi₀_linear :
      ‖lam i₀ - l‖ < ε :=
    (sq_lt_sq₀ (norm_nonneg _) (le_of_lt he)).1 hi₀
  -- Step 11: package the eigenvalue and conclude.
  have h_eig : HasEigenvalue T (lam i₀) := by
    simpa [lam] using hSym.hasEigenvalue_eigenvalues hn i₀
  refine ⟨⟨lam i₀, h_eig⟩, ?_⟩
  -- Step 11.1: rewrite the norm in the requested order.
  simpa [lam, norm_sub_rev] using hi₀_linear
