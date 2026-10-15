import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End InnerProductSpace
open scoped BigOperators ComplexConjugate



/-Informal Statement

Suppose $\left(e_{1}, \ldots, e_{m}\right)$ is an orthonormal list of vectors in $V$. Let $v \in V$. Prove that $\|v\|^{2}=\left|\left\langle v, e_{1}\right\rangle\right|^{2}+\cdots+\left|\left\langle v, e_{m}\right\rangle\right|^{2}$ if and only if $v \in \operatorname{span}\left(e_{1}, \ldots, e_{m}\right)$.
-/

/-Informal Proof

If $v \in \operatorname{span}\left(e_1, \ldots, e_m\right)$, it means that
$$
v=\alpha_1 e_1+\ldots+\alpha_m e_m .
$$
for some scalars $\alpha_i$. We know that $\alpha_k=\left\langle v, e_k\right\rangle, \forall k \in\{1, \ldots, m\}$. Therefore,
$$
\begin{aligned}
\|v\|^2 & =\langle v, v\rangle \\
& =\left\langle\alpha_1 e_1+\ldots+\alpha_m e_m, \alpha_1 e_1+\ldots+\alpha_m e_m\right\rangle \\
& =\left|\alpha_1\right|^2\left\langle e_1, e_1\right\rangle+\ldots+\left|\alpha_m\right|^2\left\langle e_m, e_m\right\rangle \\
& =\left|\alpha_1\right|^2+\ldots+\left|\alpha_m\right|^2 \\
& =\left|\left\langle v, e_1\right\rangle\right|^2+\ldots+\left|\left\langle v, e_m\right\rangle\right|^2 .
\end{aligned}
$$
$\Rightarrow$ Assume that $v \notin \operatorname{span}\left(e_1, \ldots, e_m\right)$. Then, we must have
$$
v=v_{m+1}+\frac{\left\langle v, v_0\right\rangle}{\left\|v_0\right\|^2} v_0,
$$
where $v_0=\alpha_1 e_1+\ldots+\alpha_m e_m, \alpha_k=\left\langle v, e_k\right\rangle, \forall k \in\{1, \ldots, m\}$, and $v_{m+1}=v-$ $\frac{\left\langle v, v_0\right\rangle}{\left\|v_0\right\|^2} v_0 \neq 0$.

We have $\left\langle v_0, v_{m+1}\right\rangle=0$ (from which we get $\left\langle v, v_0\right\rangle=\left\langle v_0, v_0\right\rangle$ and $\left\langle v, v_{m+1}\right\rangle=$ $\left.\left\langle v_{m+1}, v_{m+1}\right\rangle\right)$. Now,
$$
\begin{aligned}
\|v\|^2 & =\langle v, v\rangle \\
& =\left\langle v, v_{m+1}+\frac{\left\langle v, v_0\right\rangle}{\left\|v_0\right\|^2} v_0\right\rangle \\
& =\left\langle v, v_{m+1}\right\rangle+\left\langle v, \frac{\left\langle v, v_0\right\rangle}{\left\|v_0\right\|^2} v_0\right\rangle \\
& =\left\langle v_{m+1}, v_{m+1}\right\rangle+\frac{\left\langle v_0, v_0\right\rangle}{\left\|v_0\right\|^2}\left\langle v_0, v_0\right\rangle \\
& =\left\|v_{m+1}\right\|^2+\left\|v_0\right\|^2 \\
& >\left\|v_0\right\|^2 \\
& =\left|\alpha_1\right|^2+\ldots+\left|\alpha_m\right|^2 \\
& =\left|\left\langle v, e_1\right\rangle\right|^2+\ldots+\left|\left\langle v, e_m\right\rangle\right|^2 .
\end{aligned}
$$
By contrapositive, if $\left\|v_1\right\|^2=\left|\left\langle v, e_1\right\rangle\right|^2+\ldots+\left|\left\langle v, e_m\right\rangle\right|^2$, then $v \in \operatorname{span}\left(e_1, \ldots, e_m\right)$.
-/

theorem Axler_exercise_6_13 {V : Type*} [NormedAddCommGroup V] [RCLike F] [InnerProductSpace F V] {n : ℕ}
  {e : Fin n → V} (he : Orthonormal F e) (v : V) :
  ‖v‖^2 = ∑ i : Fin n, ‖⟪v, e i⟫_F‖^2 ↔ v ∈ Submodule.span F (e '' Set.univ) := by
  classical
  -- Step 1: Define the working submodule, the coefficient function, the projected vector, and the target sum.
  set W : Submodule F V := Submodule.span F (e '' Set.univ)
  set coeff : Fin n → F := fun i => ⟪e i, v⟫_F
  set proj : V := ∑ i : Fin n, coeff i • e i
  set S : ℝ := ∑ i : Fin n, ‖⟪v, e i⟫_F‖^2
  -- Step 1.1: Every summand of `proj` lies in the span, hence so does `proj`.
  have h_proj_mem : proj ∈ W := by
    unfold proj
    refine Finset.induction_on (Finset.univ : Finset (Fin n)) ?base ?step
    · -- Step 1.1.1: The empty sum is zero, which is in every submodule.
      simp
    · intro a s ha hs
      -- Step 1.1.2: Additivity of the submodule keeps the partial sums inside.
      have hterm :
          coeff a • e a ∈ W := by
        refine W.smul_mem (coeff a) ?_
        refine Submodule.subset_span ?_
        exact ⟨a, Set.mem_univ _, rfl⟩
      simpa [Finset.sum_insert ha, add_comm, add_left_comm, add_assoc] using
        W.add_mem hterm hs
  -- Step 1.2: Replace the target sum with the norm of the coefficient vector defined using ⟪e i, v⟫.
  have h_sum_rewrite :
      S = ∑ i : Fin n, ‖coeff i‖^2 := by
    unfold S
    refine Finset.sum_congr rfl fun i _ => ?_
    -- Step 1.2.1: Conjugate symmetry shows the two coefficient choices have equal norms.
    have hinner : ⟪v, e i⟫_F = conj (coeff i) := by
      simp [coeff, inner_conj_symm]
    have hnorm : ‖⟪v, e i⟫_F‖ = ‖coeff i‖ := by
      simp [hinner]
    simp [hnorm]
  -- Step 1.3: Relate ‖proj‖² to the rewritten sum by evaluating ⟪proj, proj⟫ explicitly.
  have h_proj_sq :
      ‖proj‖^2 = ∑ i : Fin n, ‖coeff i‖^2 := by
    -- Step 1.3.1: Expand the inner product of the orthogonal projection with itself.
    have h_inner :
        ⟪proj, proj⟫_F = (∑ i : Fin n, ‖coeff i‖^2 : ℝ) := by
      have h_sum := he.inner_sum coeff coeff (Finset.univ : Finset (Fin n))
      -- Step 1.3.2: Orthogonality makes all cross terms vanish, leaving conjugate-times-coefficient.
      simp at h_sum
      have h_rhs :
          (∑ i : Fin n, conj (coeff i) * coeff i)
            = (∑ i : Fin n, (‖coeff i‖^2 : ℝ)) := by
        simp [RCLike.conj_mul]
      rw [inner_self_eq_norm_sq_to_K]
      exact_mod_cast h_sum.trans h_rhs
    -- Step 1.3.3: Convert the equality inside `F` back to an equality of real numbers.
    have h_inner' :
        ((‖proj‖ : ℝ)^2 : F) = (∑ i : Fin n, ‖coeff i‖^2 : ℝ) := by
      have := (inner_self_eq_norm_sq_to_K (𝕜 := F) proj).symm.trans h_inner
      simpa using this
    -- Step 1.3.4: Use injectivity of the real embedding to conclude the desired real equality.
    exact_mod_cast h_inner'
  -- Step 1.4: Record that `v - proj` is orthogonal to every `e i`, which will drive both directions.
  have h_diff_inner (i : Fin n) : ⟪v - proj, e i⟫_F = 0 := by
    -- Step 1.4.1: Compare the coefficients of `v` and `proj` along `e i`.
    have h_proj_coeff :
        ⟪proj, e i⟫_F = ⟪v, e i⟫_F := by
      have h_right :
          ⟪e i, proj⟫_F = coeff i := by
        simpa [proj, coeff] using he.inner_right_fintype coeff i
      -- Step 1.4.2: Conjugate symmetry transfers equality from ⟪e i, ·⟫ to ⟪·, e i⟫.
      simpa [coeff, inner_conj_symm] using congrArg conj h_right
    -- Step 1.4.3: Subtracting equal coefficients yields the claimed orthogonality.
    simp [inner_sub_left, h_proj_coeff]
  -- Step 1.5: Consequently, `v - proj` is orthogonal to `proj` itself.
  have h_diff_proj :
      ⟪v - proj, proj⟫_F = 0 := by
    -- Step 1.5.1: Expand against the sum definition of `proj` to see each term vanish.
    simp [proj, inner_sum, inner_smul_right, h_diff_inner]
  -- Step 1.6: Turn orthogonality into a Pythagorean identity relating ‖v‖², S, and ‖v - proj‖².
  have h_norm_decomp :
      ‖v‖^2 = S + ‖v - proj‖^2 := by
    -- Step 1.6.1: Apply the norm-square Pythagorean theorem to `(v - proj) + proj = v`.
    have h_py :
        ‖(v - proj) + proj‖ * ‖(v - proj) + proj‖ =
          ‖v - proj‖ * ‖v - proj‖ + ‖proj‖ * ‖proj‖ :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (v - proj) proj h_diff_proj
    have h_py' : ‖v‖^2 = ‖v - proj‖^2 + ‖proj‖^2 := by
      simpa [pow_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_py
    -- Step 1.6.2: Substitute the previously established identities for the projection term.
    simpa [S, h_sum_rewrite, h_proj_sq, add_comm] using h_py'
  -- Step 2: Prove the “only if” direction using the vanishing remainder.
  constructor
  · intro h_eq
    -- Step 2.1: Comparing `h_eq` with the Pythagorean decomposition forces the remainder norm to vanish.
    have h_cancel :
        S = S + ‖v - proj‖^2 := by
      simpa [S] using h_eq.symm.trans h_norm_decomp
    have h_zero' : 0 = ‖v - proj‖^2 := by
      have := congrArg (fun t : ℝ => t - S) h_cancel
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have h_zero : ‖v - proj‖^2 = 0 := by simpa using h_zero'.symm
    -- Step 2.2: A zero norm shows the vector itself vanishes, hence `v = proj`.
    have h_norm_zero : ‖v - proj‖ = 0 := by
      have : ‖v - proj‖ * ‖v - proj‖ = 0 := by
        simpa [sq, mul_comm] using h_zero
      exact mul_self_eq_zero.mp this
    have h_vec_zero : v - proj = 0 := norm_eq_zero.mp h_norm_zero
    have hv_eq_proj : v = proj := sub_eq_zero.mp h_vec_zero
    -- Step 2.3: Substituting `v = proj` gives the desired span membership.
    simpa [hv_eq_proj] using h_proj_mem
  -- Step 3: Prove the “if” direction by showing the orthogonal complement part must be zero.
  · intro hv_mem
    -- Step 3.1: The difference of two members of the span is still inside the span.
    have h_diff_mem : v - proj ∈ W := by
      simpa using W.sub_mem hv_mem h_proj_mem
    -- Step 3.2: Show that `v - proj` also lies in `Wᗮ` by span induction.
    have h_diff_orth :
        v - proj ∈ Wᗮ := by
      -- Step 3.2.1: Verify the defining property of orthogonality against arbitrary span elements.
      refine (W.mem_orthogonal (v - proj)).2 ?_
      intro u hu
      -- Step 3.2.2: Use span induction where the predicate states “inner product equals zero”.
      refine Submodule.span_induction (p := fun x _ => ⟪x, v - proj⟫_F = 0)
          (s := e '' Set.univ)
          (mem := ?_) (zero := by simp)
          (add := ?_) (smul := ?_) hu
      · -- Step 3.2.2.1: The predicate holds on every generator `e i`.
        intro x hx
        rcases hx with ⟨i, -, rfl⟩
        -- Step 3.2.2.2: Symmetry relates this to the already established orthogonality.
        simpa [inner_conj_symm] using congrArg conj (h_diff_inner i)
      · -- Step 3.2.2.3: The predicate is stable under addition.
        intro x y hx hy hx0 hy0
        simp [inner_add_left, hx0, hy0]
      · -- Step 3.2.2.4: The predicate is stable under scalar multiplication.
        intro a x hx hx0
        simp [inner_smul_left, hx0]
    -- Step 3.3: Intersecting the span with its orthogonal complement yields only the zero vector.
    have h_bot :
        v - proj ∈ (⊥ : Submodule F V) := by
      have : v - proj ∈ W ⊓ Wᗮ := ⟨h_diff_mem, h_diff_orth⟩
      simpa [Submodule.inf_orthogonal_eq_bot] using this
    have h_vec_zero : v - proj = 0 := by
      simpa using h_bot
    -- Step 3.4: With `v = proj`, combine the previous norm identity to finish the equality.
    have hv_eq_proj : v = proj := sub_eq_zero.mp h_vec_zero
    calc
      ‖v‖^2 = ‖proj‖^2 := by simp [hv_eq_proj]
      _ = ∑ i : Fin n, ‖coeff i‖^2 := h_proj_sq
      _ = S := by simp [h_sum_rewrite]
