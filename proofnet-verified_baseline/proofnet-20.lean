import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators



/-Informal Statement

Suppose $T \in \mathcal{L}(V)$ is such that every vector in $V$ is an eigenvector of $T$. Prove that $T$ is a scalar multiple of the identity operator.
-/

/-Informal Proof

For every single $v \in V$, there does exist $a_v \in F$ such that $T v=a_v v$. Since $T 0=0$, then we have to make $a_0$ be the any number in F. However, for every single $v \in V\{0\}$, then the value of $a_V$ is uniquely determined by the previous equation of $T v=a_v v$.

Now, to show that $T$ is a scalar multiple of the identity, then me must show that $a_v$ is independent of $v$ for $v \in V\{0\}$. We would now want to show that $a_v=a_w$.

First, just make the case of where $(v, w)$ is linearly dependent. Then, there does exist $b \in F$ such that $w=b v$. Now, you would have the following: $a_W w=T w=T(b v)=b T v=b\left(a_v v\right)=a_v w$. This is showing that $a_v=a_w$.
Finally, make the consideration to make $(v, w)$ be linearly independent. Now, we would have the following: $\left.a_{(} v+w\right)(v+w)=T(v+w)=T v+T w=a_v v+a_w w$.

That previous equation implies the following: $\left.\left.\left(a_{(} v+w\right)-a_v\right) v+\left(a_{(} v+w\right)-a_w\right) w=0$. Since $(v, w)$ is linearly independent, this would imply that both $\left.a_{(} v+w\right)=a_v$ and $\left.a_{(} v+w\right)=a_w$. Therefore, $a_v=a_w$.
-/

theorem Axler_exercise_5_12 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] {S : End F V}
  (hS : ∀ v : V, ∃ c : F, v ∈ eigenspace S c) :
  ∃ c : F, S = c • LinearMap.id := by
  -- Step 1: Enable classical choice to pick eigenvalues for individual vectors.
  classical
  -- Step 2: Define a helper that records one eigenvalue for every vector.
  let eig : V → F := fun v => Classical.choose (hS v)
  -- Step 2.1: Store the fact that each vector indeed lies in its chosen eigenspace.
  have heig : ∀ v : V, v ∈ eigenspace S (eig v) :=
    fun v => Classical.choose_spec (hS v)
  -- Step 2.2: Rewrite the eigenspace membership as the concrete eigenvector equation.
  have heq : ∀ v : V, S v = (eig v) • v := fun v => by
    -- Step 2.2.1: Apply the characterization of membership in an eigenspace.
    simpa [eig, Module.End.mem_eigenspace_iff] using heig v
  -- Step 3: Separate the degenerate case where every vector is zero from the nontrivial case.
  by_cases hNontrivial : ∃ v : V, v ≠ 0
  -- Step 4: Handle the interesting case with a genuine nonzero vector.
  · obtain ⟨v₀, hv₀⟩ := hNontrivial
    -- Step 4.1: Let μ be the eigenvalue attached to our chosen nonzero vector.
    set μ : F := eig v₀
    -- Step 4.1.1: Record the defining equation for μ.
    have hμ_spec : S v₀ = μ • v₀ := by
      -- Step 4.1.1.1: Unfold the helper equality.
      simpa [μ] using heq v₀
    -- Step 4.2: Show that μ works for every vector by comparing images on arbitrary inputs.
    refine ⟨μ, ?_⟩
    -- Step 4.2.1: Two linear maps are equal if they agree on every vector.
    ext w
    -- Step 4.2.2: Distinguish the trivial input vector.
    by_cases hw : w = 0
    -- Step 4.2.2.1: When the input is zero, both sides vanish immediately.
    · simp [hw, LinearMap.map_zero]
    -- Step 4.2.3: Work under the assumption that the input is nonzero.
    · -- Step 4.2.3.1: Split into the subcase where w lies on the line spanned by v₀.
      by_cases hDep : ∃ a : F, w = a • v₀
      -- Step 4.2.3.1.1: If dependent, a short scalar-multiplication computation proves the claim.
      · obtain ⟨a, rfl⟩ := hDep
        -- Step 4.2.3.1.1.1: Push the scalar through the linear map and compare.
        calc
          S (a • v₀) = a • S v₀ := by
            -- Step 4.2.3.1.1.1.1: A linear map respects scalar multiplication.
            exact S.map_smul a v₀
          _ = a • (μ • v₀) := by
            -- Step 4.2.3.1.1.1.2: Substitute the defining relation for μ.
            simp [hμ_spec]
          _ = μ • (a • v₀) := by
            -- Step 4.2.3.1.1.1.3: Reassociate the scalar product.
            simp [mul_comm, smul_smul]
      -- Step 4.2.3.2: Treat the independent case where w is not a multiple of v₀.
      · push_neg at hDep
        -- Step 4.2.3.2.1: Introduce shorthand for the eigenvalues of w and v₀ + w.
        set μw : F := eig w
        set μ' : F := eig (v₀ + w)
        -- Step 4.2.3.2.2: Register the eigenvector equations for w and v₀ + w.
        have hSw : S w = μw • w := by
          simpa [μw] using heq w
        have hSsum : S (v₀ + w) = μ' • (v₀ + w) := by
          simpa [μ'] using heq (v₀ + w)
        -- Step 4.2.3.2.3: Compare the two different ways of expanding S (v₀ + w).
        have hCombine :
            μ • v₀ + μw • w = μ' • v₀ + μ' • w := by
          calc
            μ • v₀ + μw • w
                = S v₀ + S w := by
                  -- Step 4.2.3.2.3.1: Replace both summands by their S-images.
                  simp [hμ_spec, hSw]
            _ = S (v₀ + w) := by
                  -- Step 4.2.3.2.3.2: Use linearity of S on sums.
                  exact (S.map_add v₀ w).symm
            _ = μ' • (v₀ + w) := hSsum
            _ = μ' • v₀ + μ' • w := by
                  -- Step 4.2.3.2.3.3: Expand the scalar multiplication across the sum.
                  simp [smul_add]
        -- Step 4.2.3.2.4: Isolate the relation involving the three eigenvalues.
        have hRelation :
            μ • v₀ - μ' • v₀ = μ' • w - μw • w := by
          -- Step 4.2.3.2.4.1: Move both extra terms to the left-hand side at once.
          have hSub := congrArg (fun x => x - μ' • v₀ - μw • w) hCombine
          -- Step 4.2.3.2.4.2: Simplify the resulting difference of sums.
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hSub
        have hRelation' :
            (μ - μ') • v₀ = (μ' - μw) • w := by
          -- Step 4.2.3.2.4.3: Convert the differences into scalar multiples.
          simpa [sub_smul] using hRelation
        -- Step 4.2.3.2.5: First show that μw must equal μ'.
        have hμw_eq_μ' : μw = μ' := by
          -- Step 4.2.3.2.5.1: A contradiction arises if the eigenvalues differed.
          by_contra hNe
          -- Step 4.2.3.2.5.2: Use the relation to write w as a scalar multiple of v₀.
          have hScalar : μ' - μw ≠ 0 := sub_ne_zero.mpr (Ne.symm hNe)
          have hMultiple :
              w = ((μ - μ') * (μ' - μw)⁻¹) • v₀ := by
            -- Step 4.2.3.2.5.2.1: Multiply the relation by the inverse scalar.
            have := congrArg (fun z => (μ' - μw)⁻¹ • z) hRelation'.symm
            -- Step 4.2.3.2.5.2.2: Simplify to isolate w.
            have hScaled :
                (1 : F) • w = ((μ' - μw)⁻¹ * (μ - μ')) • v₀ := by
              simpa [smul_smul, hScalar] using this
            -- Step 4.2.3.2.5.2.3: Rewrite the coefficient to the target orientation.
            calc
              w = (1 : F) • w := by simp
              _ = ((μ' - μw)⁻¹ * (μ - μ')) • v₀ := by
                simpa using hScaled
              _ = ((μ - μ') * (μ' - μw)⁻¹) • v₀ := by
                simp [mul_comm]
          -- Step 4.2.3.2.5.3: Contradict the assumption that w is not in the span of v₀.
          have hContr := hDep ((μ - μ') * (μ' - μw)⁻¹)
          exact hContr hMultiple
        -- Step 4.2.3.2.6: With μw = μ', the relation reduces to (μ - μ') • v₀ = 0.
        have hμ_eq_μ' : μ = μ' := by
          -- Step 4.2.3.2.6.1: Substitute μw = μ' in the relation.
          have hZero : (μ - μ') • v₀ = 0 := by
            simpa [hμw_eq_μ', sub_self] using hRelation'
          -- Step 4.2.3.2.6.2: If μ ≠ μ', inverting the scalar would force v₀ = 0.
          by_contra hNe
          have hScalar : μ - μ' ≠ 0 := sub_ne_zero.mpr hNe
          have hv₀_zero : v₀ = 0 := by
            have := congrArg (fun z => (μ - μ')⁻¹ • z) hZero
            have : ((μ - μ')⁻¹ * (μ - μ')) • v₀ = 0 := by
              simpa [smul_smul] using this
            have : (1 : F) • v₀ = 0 := by
              simpa [hScalar] using this
            simpa using this
          exact hv₀ hv₀_zero
        -- Step 4.2.3.2.7: Conclude that μw equals μ.
        have hμw_eq_μ : μw = μ := by
          calc
            μw = μ' := hμw_eq_μ'
            _ = μ := hμ_eq_μ'.symm
        -- Step 4.2.3.2.8: Finish by rewriting S w with the shared eigenvalue.
        simp [hSw, hμw_eq_μ]
  -- Step 5: Address the purely degenerate case where every vector is zero.
  · have hAllZero : ∀ v : V, v = 0 := by
      -- Step 5.1: Show every vector must equal zero under the negated existence hypothesis.
      intro v
      by_contra hv
      exact hNontrivial ⟨v, hv⟩
    -- Step 5.2: In this case, the linear map is the zero map, i.e., 0 • id.
    refine ⟨0, ?_⟩
    -- Step 5.3: Check equality on every vector.
    ext v
    -- Step 5.3.1: Reduce to evaluating the map at the zero vector.
    have hv : v = 0 := hAllZero v
    -- Step 5.3.2: Simplify both sides using the helper equation.
    have hS_zero : S v = 0 := by
      cases hv
      simp
    have hZeroMap_apply : ((0 : F) • LinearMap.id : End F V) v = 0 := by
      simp
    exact hS_zero.trans hZeroMap_apply.symm
