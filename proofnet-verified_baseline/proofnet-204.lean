import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators


/-
Auxiliary lemma (copied from an earlier exercise, proofnet-17 i.e. Axler|exercise_3_1):
every linear map on a one-dimensional vector space is multiplication by a scalar.
We will use this for quotient spaces of dimension `1`.
-/

theorem exercise_3_1 {F V : Type*}
  [AddCommGroup V] [Field F] [Module F V] [FiniteDimensional F V]
  (T : V →ₗ[F] V) (hT : finrank F V = 1) :
  ∃ c : F, ∀ v : V, T v = c • v:= by
  -- Step 1: Work in the classical logic universe so that we can choose concrete witnesses.
  classical
  -- Step 2: Extract a specific nonzero vector witnessing that the finrank is positive.
  have hpos : 0 < finrank F V := by
    -- Step 2.1: The hypothesis `finrank F V = 1` implies positivity directly.
    simp [hT]
  -- Step 2.2: Turn the positivity statement into the existence of a nonvanishing vector.
  obtain ⟨x, hx⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := F) (M := V)).1 hpos
  -- Step 3: Because the space is one-dimensional, `T x` must be a scalar multiple of `x`.
  obtain ⟨c, hc⟩ :=
    exists_smul_eq_of_finrank_eq_one (K := F) (V := V) (x := x) hT hx (T x)
  -- Step 4: Show that the same scalar `c` works for every vector of the space.
  refine ⟨c, ?_⟩
  -- Step 4.1: Fix an arbitrary vector and express it as a scalar multiple of `x`.
  intro v
  -- Step 4.1.1: Use the one-dimensionality lemma again to write `v = a • x`.
  obtain ⟨a, ha⟩ :=
    exists_smul_eq_of_finrank_eq_one (K := F) (V := V) (x := x) hT hx v
  -- Step 4.2: Transport the equality `v = a • x` through the linear map and compare both sides.
  calc
    T v = T (a • x) := by
      -- Step 4.2.1: Replace `v` with its scalar-multiple representation.
      simp [ha]
    _ = a • T x := by
      -- Step 4.2.2: A linear map respects scalar multiplication.
      simp [T.map_smul a x]
    _ = a • (c • x) := by
      -- Step 4.2.3: Substitute the defining relation for `c`.
      simp [hc]
    _ = (a * c) • x := by
      -- Step 4.2.4: Collapse the nested scalar multiplication.
      simp [mul_comm, smul_smul a c x]
    _ = (c * a) • x := by
      -- Step 4.2.5: Commute the scalars inside the product (the field multiplication is commutative).
      simp [mul_comm]
    _ = c • (a • x) := by
      -- Step 4.2.6: Expand the product back into iterated scalar multiplication.
      simp [smul_smul c a x]
    _ = c • v := by
      -- Step 4.2.7: Return to the original expression for `v`.
      simp [ha]

/-
Auxiliary lemma (copied from an earlier excercise, proofnet-20 i.e. Axler|exercise_5_12): if every vector of a module is an eigenvector
of an endomorphism `S`, then `S` is a scalar multiple of the identity.
We will apply this lemma to the dual map `T.dualMap` on the dual space.
-/

theorem exercise_5_12 {F V : Type*} [AddCommGroup V] [Field F]
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


/-Informal Statement

Suppose $T \in \mathcal{L}(V)$ is such that every subspace of $V$ with dimension $\operatorname{dim} V-1$ is invariant under $T$. Prove that $T$ is a scalar multiple of the identity operator.
-/

/-Informal Proof

First off, let $T$ isn't a scalar multiple of the identity operator. So, there does exists that $v \in V$ such that $u$ isn't an eigenvector of $T$. Therefore, $(u, T u)$ is linearly independent.

Next, you should extend $(u, T u)$ to a basis of $\left(u, T u, v_1, \ldots, v_n\right)$ of $V$. So, let $U=\operatorname{span}\left(u, v_1, \ldots, v_n\right)$. Then, $U$ is a subspace of $V$ and $\operatorname{dim} U=\operatorname{dim} V-1$. However, $U$ isn't invariant under $T$ since both $u \in U$ and $T u \in U$. This given contradiction to our hypothesis about $T$ actually shows us that our guess that $T$ is not a scalar multiple of the identity must have been false.
-/


theorem Axler_exercise_5_13 {F V : Type*} [AddCommGroup V] [Field F]
    [Module F V] [FiniteDimensional F V] {T : End F V}
    (hS : ∀ U : Submodule F V, finrank F U = finrank F V - 1 →
      Submodule.map T U = U) : ∃ c : F, T = c • LinearMap.id := by
  -- Step 1: Work classically to use choice.
  classical
  -- Step 2: Introduce the dual endomorphism `S = T.dualMap` on the dual space.
  let S : End F (Module.Dual F V) := T.dualMap
  ---------------------------------------------------------------------------
  -- Step 3: For a nonzero functional `φ`, construct an eigenvalue `c` such   --
  --         that `φ.comp T = c • φ` using the hypothesis on codimension-1    --
  --         invariant subspaces and the one-dimensional quotient.           --
  ---------------------------------------------------------------------------
  have hEigen_nonzero :
      ∀ φ : Module.Dual F V, φ ≠ 0 → ∃ c : F, (φ.comp T) = c • φ := by
    intro φ hφ_ne
    -- Step 3.1: Let `U` be the kernel of `φ`, a codimension-1 subspace.
    let U : Submodule F V := LinearMap.ker (φ : V →ₗ[F] F)
    -- Step 3.1.1: Use the dual-space lemma to compute the finrank of the kernel.
    have hKerAdd :
        finrank F U + 1 = finrank F V := by
      simpa [U] using
        (Module.Dual.finrank_ker_add_one_of_ne_zero (K := F) (V₁ := V)
          (f := φ) hφ_ne)
    -- Step 3.1.2: Rewrite this as `finrank F U = finrank F V - 1` to apply `hS`.
    have hDimU : finrank F U = finrank F V - 1 := by
      have := congrArg (fun n : ℕ => n - 1) hKerAdd
      simpa [U, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
    -- Step 3.2: Invoke the hypothesis to see that `U` is invariant under `T`.
    have hmap : Submodule.map T U ≤ U := (hS U hDimU).le
    -- Step 3.2.1: Translate `map T U ≤ U` into the inclusion `U ≤ comap T U`.
    have hInvariant : U ≤ Submodule.comap T U := by
      intro x hx
      -- `T x` belongs to the image `map T U`, which is contained in `U`.
      have hx_im : T x ∈ Submodule.map T U := ⟨x, hx, rfl⟩
      -- Use the inclusion `map T U ≤ U` to conclude `T x ∈ U`.
      exact hmap hx_im
    -- Step 3.3: Form the induced endomorphism on the quotient `V ⧸ U`.
    let Tbar : (V ⧸ U) →ₗ[F] V ⧸ U := U.mapQ U T hInvariant
    -- Step 3.4: Compute the finrank of the quotient, using two rank-nullity identities.
    have hQuotAdd :
        finrank F (V ⧸ U) + finrank F U = finrank F V :=
      Submodule.finrank_quotient_add_finrank (R := F) (M := V) U
    -- Step 3.4.1: Combine `hQuotAdd` with the kernel identity to see `finrank (V ⧸ U) = 1`.
    have hQuotDim : finrank F (V ⧸ U) = 1 := by
      have h' :
          finrank F (V ⧸ U) + finrank F U = finrank F U + 1 :=
        hQuotAdd.trans hKerAdd.symm
      have h'' :
          finrank F U + finrank F (V ⧸ U) = finrank F U + 1 := by
        simpa [Nat.add_comm] using h'
      exact Nat.add_left_cancel h''
    -- Step 3.5: Apply the one-dimensional lemma to `Tbar`.
    obtain ⟨c, hc⟩ :=
      exercise_3_1 (F := F) (V := V ⧸ U) (T := Tbar) hQuotDim
    -- Step 3.6: Use the action of `Tbar` on the equivalence classes `[v]` to relate `T` and `φ`.
    have hAction : ∀ v : V, (φ.comp T) v = c • φ v := by
      intro v
      -- Step 3.6.1: Evaluate the scalar relation on the class of `v`.
      have hQuot :
          (Submodule.Quotient.mk (T v) : V ⧸ U) =
            (Submodule.Quotient.mk (c • v) : V ⧸ U) := by
        -- `hc` says `Tbar z = c • z` for every `z`; specialize to `[v]`.
        have h := hc (Submodule.Quotient.mk v)
        -- Compute both sides via the definition of `Tbar` and the quotient operations.
        simpa [Tbar] using h
      -- Step 3.6.2: Translate the quotient equality into membership in the kernel `U`.
      have hMem : T v - c • v ∈ U :=
        (Submodule.Quotient.eq (p := U)).mp hQuot
      -- Step 3.6.3: Membership in `U = ker φ` means the functional vanishes on this difference.
      have hφ_zero : φ (T v - c • v) = 0 := by
        simpa [U, LinearMap.mem_ker] using hMem
      -- Step 3.6.4: Expand the image of the difference via linearity of `φ`.
      have hEqSub : φ (T v) - c • φ v = 0 := by
        simpa [LinearMap.map_sub, LinearMap.map_smul] using hφ_zero
      -- Step 3.6.5: Simplify to get the scalar-eigenvalue relation `φ (T v) = c • φ v`.
      have hEq : φ (T v) = c • φ v := sub_eq_zero.mp hEqSub
      -- Step 3.6.6: Reinterpret this as an equality for `(φ.comp T) v`.
      simpa [LinearMap.comp_apply] using hEq
    -- Step 3.7: Package the pointwise relation into an equality of linear maps.
    refine ⟨c, ?_⟩
    -- Two linear maps are equal if they agree on every vector.
    ext v
    exact hAction v
  ---------------------------------------------------------------------------
  -- Step 4: Every functional (including `0`) is an eigenvector of the dual  --
  --         map `S = T.dualMap`.                                            --
  ---------------------------------------------------------------------------
  have hEigenDual :
      ∀ φ : Module.Dual F V, ∃ c : F, φ ∈ eigenspace S c := by
    intro φ
    -- Step 4.1: Split into the zero and nonzero cases.
    by_cases hφ : φ = 0
    -- Step 4.1.1: The zero functional is an eigenvector with eigenvalue `0`.
    · refine ⟨0, ?_⟩
      simp [S, hφ]
    -- Step 4.1.2: For nonzero `φ`, reuse `hEigen_nonzero` and rewrite via `dualMap`.
    · have hφ_ne : φ ≠ 0 := hφ
      obtain ⟨c, hc⟩ := hEigen_nonzero φ hφ_ne
      refine ⟨c, ?_⟩
      -- Convert `φ.comp T = c • φ` into `S φ = c • φ`.
      have hEq : S φ = c • φ := by
        simpa [S, LinearMap.dualMap_apply'] using hc
      -- Membership in the eigenspace is exactly this equality.
      simpa [Module.End.mem_eigenspace_iff] using hEq
  ---------------------------------------------------------------------------
  -- Step 5: Apply the general lemma to conclude that the dual map is a     --
  --         scalar multiple of the identity.                               --
  ---------------------------------------------------------------------------
  obtain ⟨c, hScalarDual⟩ :=
    exercise_5_12 (F := F) (V := Module.Dual F V) (S := S) hEigenDual
  ---------------------------------------------------------------------------
  -- Step 6: Use duality to show that `T` itself is `c • id`.               --
  ---------------------------------------------------------------------------
  refine ⟨c, ?_⟩
  -- Step 6.1: Show that `T v - c • v = 0` for every `v`, using separation by dual functionals.
  ext v
  -- Consider the vector `w = T v - c • v` and show all functionals vanish on it.
  have hAllZero : ∀ φ : Module.Dual F V, φ (T v - c • v) = 0 := by
    intro φ
    -- Step 6.1.1: Extract the equality `S φ = c • φ` from `hScalarDual`.
    have hφ' := congrArg (fun L : Module.Dual F V →ₗ[F] Module.Dual F V => L φ) hScalarDual
    -- Step 6.1.2: Rewrite both sides using the definitions of `S` and scalar multiples.
    have hComp : φ.comp T = c • φ := by
      simpa [S, LinearMap.dualMap_apply', LinearMap.smul_apply] using hφ'
    -- Step 6.1.3: Evaluate this equality at the vector `v`.
    have hComp_v :
        (φ.comp T) v = (c • φ) v := congrArg (fun f : V →ₗ[F] F => f v) hComp
    -- Step 6.1.4: Simplify both sides to obtain `φ (T v) = c • φ v`.
    have hφTv : φ (T v) = c • φ v := by
      simpa [LinearMap.comp_apply, LinearMap.smul_apply] using hComp_v
    -- Step 6.1.5: Use linearity of `φ` to compute `φ (T v - c • v)`.
    simp [LinearMap.map_sub, hφTv]
  -- Step 6.2: Dual functionals separate points, so `T v - c • v = 0`.
  have hDiff_zero :
      T v - c • v = (0 : V) :=
    (Module.forall_dual_apply_eq_zero_iff (R := F) (V := V) (v := T v - c • v)).mp hAllZero
  -- Step 6.3: Rearrange to the desired equality `T v = c • v`.
  have hTv : T v = c • v := sub_eq_zero.mp hDiff_zero
  -- Step 6.4: Use this pointwise equality to conclude equality of linear maps.
  simpa using hTv


theorem Axler_exercise_5_13_corrected {F V : Type*} [AddCommGroup V] [Field F]
    [Module F V] [FiniteDimensional F V] {T : End F V}
    (hS : ∀ U : Submodule F V, finrank F U = finrank F V - 1 →
      Submodule.map T U ≤ U) : ∃ c : F, T = c • LinearMap.id := by
  -- Step 1: Work classically to use choice.
  classical
  -- Step 2: Introduce the dual endomorphism `S = T.dualMap` on the dual space.
  let S : End F (Module.Dual F V) := T.dualMap
  ---------------------------------------------------------------------------
  -- Step 3: For a nonzero functional `φ`, construct an eigenvalue `c` such   --
  --         that `φ.comp T = c • φ` using the hypothesis on codimension-1    --
  --         invariant subspaces and the one-dimensional quotient.           --
  ---------------------------------------------------------------------------
  have hEigen_nonzero :
      ∀ φ : Module.Dual F V, φ ≠ 0 → ∃ c : F, (φ.comp T) = c • φ := by
    intro φ hφ_ne
    -- Step 3.1: Let `U` be the kernel of `φ`, a codimension-1 subspace.
    let U : Submodule F V := LinearMap.ker (φ : V →ₗ[F] F)
    -- Step 3.1.1: Use the dual-space lemma to compute the finrank of the kernel.
    have hKerAdd :
        finrank F U + 1 = finrank F V := by
      -- `Module.Dual.finrank_ker_add_one_of_ne_zero` gives this identity.
      simpa [U] using
        (Module.Dual.finrank_ker_add_one_of_ne_zero (K := F) (V₁ := V)
          (f := φ) hφ_ne)
    -- Step 3.1.2: Rewrite this as `finrank F U = finrank F V - 1` to apply `hS`.
    have hDimU : finrank F U = finrank F V - 1 := by
      -- Apply `(· - 1)` to both sides and simplify the left.
      have := congrArg (fun n : ℕ => n - 1) hKerAdd
      -- On the left we get `(finrank F U + 1) - 1 = finrank F U`.
      simpa [U, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
    -- Step 3.2: Invoke the hypothesis to see that `U` is invariant under `T`.
    have hmap : Submodule.map T U ≤ U := hS U hDimU
    -- Step 3.2.1: Translate `map T U ≤ U` into the inclusion `U ≤ comap T U`.
    have hInvariant : U ≤ Submodule.comap T U := by
      intro x hx
      -- `T x` belongs to the image `map T U`, which is contained in `U`.
      have hx_im : T x ∈ Submodule.map T U := ⟨x, hx, rfl⟩
      -- Use the inclusion `map T U ≤ U` to conclude `T x ∈ U`.
      exact hmap hx_im
    -- Step 3.3: Form the induced endomorphism on the quotient `V ⧸ U`.
    let Tbar : (V ⧸ U) →ₗ[F] V ⧸ U := U.mapQ U T hInvariant
    -- Step 3.4: Compute the finrank of the quotient, using two rank–nullity identities.
    have hQuotAdd :
        finrank F (V ⧸ U) + finrank F U = finrank F V :=
      Submodule.finrank_quotient_add_finrank (R := F) (M := V) U
    -- Combine `hQuotAdd` with the kernel identity to see `finrank (V ⧸ U) = 1`.
    have hQuotDim : finrank F (V ⧸ U) = 1 := by
      -- Step 3.4.1: Eliminate `finrank F V` between the two equalities.
      have h' :
          finrank F (V ⧸ U) + finrank F U = finrank F U + 1 := by
        exact hQuotAdd.trans hKerAdd.symm
      -- Step 3.4.2: Rewrite the left side to cancel `finrank F U` via `Nat.add_left_cancel`.
      have h'' :
          finrank F U + finrank F (V ⧸ U) = finrank F U + 1 := by
        simpa [Nat.add_comm] using h'
      exact Nat.add_left_cancel h''
    -- Step 3.5: Apply the one-dimensional lemma to `Tbar`.
    obtain ⟨c, hc⟩ :=
      exercise_3_1 (F := F) (V := V ⧸ U) (T := Tbar) hQuotDim
    -- Step 3.6: Use the action of `Tbar` on the equivalence classes `[v]` to relate `T` and `φ`.
    have hAction : ∀ v : V, (φ.comp T) v = c • φ v := by
      intro v
      -- Step 3.6.1: Evaluate the scalar relation on the class of `v`.
      have hQuot :
          (Submodule.Quotient.mk (T v) : V ⧸ U) =
            (Submodule.Quotient.mk (c • v) : V ⧸ U) := by
        -- `hc` says `Tbar z = c • z` for every `z`; specialize to `[v]`.
        have h := hc (Submodule.Quotient.mk v)
        -- Compute both sides via the definition of `Tbar` and the quotient operations.
        simpa [Tbar] using h
      -- Step 3.6.2: Translate the quotient equality into membership in the kernel `U`.
      have hMem : T v - c • v ∈ U :=
        (Submodule.Quotient.eq (p := U)).mp hQuot
      -- Step 3.6.3: Membership in `U = ker φ` means the functional vanishes on this difference.
      have hφ_zero : φ (T v - c • v) = 0 := by
        simpa [U, LinearMap.mem_ker] using hMem
      -- Step 3.6.4: Expand the image of the difference via linearity of `φ`.
      have hEqSub : φ (T v) - c • φ v = 0 := by
        simpa [LinearMap.map_sub, LinearMap.map_smul] using hφ_zero
      -- Step 3.6.5: Simplify to get the scalar-eigenvalue relation `φ (T v) = c • φ v`.
      have hEq : φ (T v) = c • φ v := sub_eq_zero.mp hEqSub
      -- Step 3.6.6: Reinterpret this as an equality for `(φ.comp T) v`.
      simpa [LinearMap.comp_apply] using hEq
    -- Step 3.7: Package the pointwise relation into an equality of linear maps.
    refine ⟨c, ?_⟩
    -- Two linear maps are equal if they agree on every vector.
    ext v
    exact hAction v
  ---------------------------------------------------------------------------
  -- Step 4: Every functional (including `0`) is an eigenvector of the dual  --
  --         map `S = T.dualMap`.                                            --
  ---------------------------------------------------------------------------
  have hEigenDual :
      ∀ φ : Module.Dual F V, ∃ c : F, φ ∈ eigenspace S c := by
    intro φ
    -- Step 4.1: Split into the zero and nonzero cases.
    by_cases hφ : φ = 0
    -- Step 4.1.1: The zero functional is an eigenvector with eigenvalue `0`.
    · refine ⟨0, ?_⟩
      -- Use the characterization of eigenspace membership.
      -- `S φ = 0` and `0 • φ = 0` when `φ = 0`.
      simp [S, hφ]
    -- Step 4.1.2: For nonzero `φ`, reuse `hEigen_nonzero` and rewrite via `dualMap`.
    · have hφ_ne : φ ≠ 0 := hφ
      obtain ⟨c, hc⟩ := hEigen_nonzero φ hφ_ne
      refine ⟨c, ?_⟩
      -- Convert `φ.comp T = c • φ` into `S φ = c • φ`.
      -- Recall that `S = T.dualMap` and `dualMap` acts by precomposition.
      have hEq : S φ = c • φ := by
        -- `LinearMap.dualMap_apply'` tells us `T.dualMap φ = φ.comp T`.
        simpa [S, LinearMap.dualMap_apply'] using hc
      -- Membership in the eigenspace is exactly this equality.
      simpa [Module.End.mem_eigenspace_iff] using hEq
  ---------------------------------------------------------------------------
  -- Step 5: Apply the general lemma to conclude that the dual map is a     --
  --         scalar multiple of the identity.                               --
  ---------------------------------------------------------------------------
  obtain ⟨c, hScalarDual⟩ :=
    exercise_5_12 (F := F) (V := Module.Dual F V) (S := S) hEigenDual
  ---------------------------------------------------------------------------
  -- Step 6: Use duality to show that `T` itself is `c • id`.               --
  ---------------------------------------------------------------------------
  refine ⟨c, ?_⟩
  -- Step 6.1: Show that `T v - c • v = 0` for every `v`, using separation by dual functionals.
  ext v
  -- Consider the vector `w = T v - c • v` and show all functionals vanish on it.
  have hAllZero : ∀ φ : Module.Dual F V, φ (T v - c • v) = 0 := by
    intro φ
    -- Step 6.1.1: Extract the equality `S φ = c • φ` from `hScalarDual`.
    have hφ' := congrArg (fun L : Module.Dual F V →ₗ[F] Module.Dual F V => L φ) hScalarDual
    -- Step 6.1.2: Rewrite both sides using the definitions of `S` and scalar multiples.
    have hComp : φ.comp T = c • φ := by
      -- Left: `S φ = T.dualMap φ = φ.comp T`.
      -- Right: `(c • id) φ = c • φ`.
      simpa [S, LinearMap.dualMap_apply', LinearMap.smul_apply] using hφ'
    -- Step 6.1.3: Evaluate this equality at the vector `v`.
    have hComp_v :
        (φ.comp T) v = (c • φ) v := congrArg (fun f : V →ₗ[F] F => f v) hComp
    -- Step 6.1.4: Simplify both sides to obtain `φ (T v) = c • φ v`.
    have hφTv : φ (T v) = c • φ v := by
      simpa [LinearMap.comp_apply, LinearMap.smul_apply] using hComp_v
    -- Step 6.1.5: Use linearity of `φ` to compute `φ (T v - c • v)`.
    simp [LinearMap.map_sub, hφTv]
  -- Step 6.2: Dual functionals separate points, so `T v - c • v = 0`.
  have hDiff_zero :
      T v - c • v = (0 : V) :=
    (Module.forall_dual_apply_eq_zero_iff (R := F) (V := V) (v := T v - c • v)).mp hAllZero
  -- Step 6.3: Rearrange to the desired equality `T v = c • v`.
  have hTv : T v = c • v := by
    -- `T v - c • v = 0` is equivalent to `T v = c • v`.
    exact sub_eq_zero.mp hDiff_zero
  -- Step 6.4: Use this pointwise equality to conclude equality of linear maps.
  simpa using hTv
