import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators ComplexConjugate



/-Informal Statement

Prove that a normal operator on a complex inner-product space is self-adjoint if and only if all its eigenvalues are real.
-/

/-Informal Proof

First off, suppose $V$ is a complex inner product space and $T \in L(V)$ is normal. If $T$ is self-adjoint, then all its eigenvalues are real. So, conversely, let all of the eigenvalues of $T$ be real. By the complex spectral theorem, there's an orthonormal basis $\left(e_1, \ldots, e_n\right)$ of $V$ consisting of eigenvectors of $T$. Thus, there exists real numbers $\lambda_1, \ldots, \lambda_n$ such that $T e_j=\lambda_j e_j$ for $j=$ $1, \ldots, n$.
The matrix of $T$ with respect to the basis of $\left(e_1, \ldots, e_n\right)$ is the diagonal matrix with $\lambda_1, \ldots, \lambda_n$ on the diagonal. So, the matrix equals its conjugate transpose. Therefore, $T=T^*$. In other words, $T$ s self-adjoint.
-/

theorem Axler_exercise_7_9 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] (T : End ℂ V)
  (hT : T * adjoint T = adjoint T * T) :
  IsSelfAdjoint T ↔ ∀ e : T.Eigenvalues, (e : ℂ).im = 0 := by
  classical
  -- ###############################################################
  -- Step 0.  Move back and forth between linear maps and
  --          continuous linear maps (all linear maps are continuous
  --          in finite dimension).
  -- ###############################################################
  haveI := FiniteDimensional.complete ℂ V
  let Tclm : V →L[ℂ] V := LinearMap.toContinuousLinearMap T
  -- Step 0.1: transport the “normal” identity to the continuous world.
  have hTCLM : Tclm * Tclm.adjoint = Tclm.adjoint * Tclm := by
    -- Step 0.1.1: push `hT` through the algebra equivalence
    have hRaw :
        Tclm * (LinearMap.toContinuousLinearMap (adjoint T)) =
          LinearMap.toContinuousLinearMap (adjoint T) * Tclm := by
      simpa using
        (congrArg (Module.End.toContinuousLinearMap (𝕜 := ℂ) (E := V)) hT)
    -- Step 0.1.2: identify the adjoint on the continuous side.
    have hAdj :
        LinearMap.toContinuousLinearMap (adjoint T) = Tclm.adjoint := by
      simpa [Tclm] using (LinearMap.adjoint_toContinuousLinearMap T)
    -- Step 0.1.3: rewrite both sides using the identification.
    simpa [hAdj] using hRaw

  -- ###############################################################
  -- Forward implication: self-adjoint ⇒ all eigenvalues are real.
  -- ###############################################################
  constructor
  · intro hSelf
    -- Step 1: self-adjointness transported to continuous operators.
    have hSelfCLM : IsSelfAdjoint Tclm :=
      (LinearMap.isSelfAdjoint_toContinuousLinearMap_iff T).2 hSelf
    -- Step 2: reinterpret as symmetry on the underlying linear map.
    have hSym : T.IsSymmetric := by
      have hSymCLM := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).1 hSelfCLM
      simpa [Tclm] using hSymCLM
    -- Step 3: symmetric operators have conjugation-invariant eigenvalues.
    intro e
    -- Step 3.1: unpack the bundled eigenvalue.
    have hEigen : T.HasEigenvalue (e : ℂ) := e.property
    -- Step 3.2: apply the conjugation lemma.
    have hConj : conj (e : ℂ) = (e : ℂ) :=
      hSym.conj_eigenvalue_eq_self hEigen
    -- Step 3.3: extract “imaginary part = 0” from `conj z = z`.
    have hImEq : -(e : ℂ).im = (e : ℂ).im := by
      have := congrArg Complex.im hConj
      simpa using this
    -- linarith turns `-x = x` into `x = 0`.
    have hImZero : (e : ℂ).im = 0 := by linarith
    exact hImZero

  -- ###############################################################
  -- Backward implication: normal + real spectrum ⇒ self-adjoint.
  -- ###############################################################
  · intro hReal
    -- Step 4: register normality of `Tclm` as a typeclass instance.
    have hNormalCLM' : IsStarNormal Tclm := by
      refine ⟨?comm⟩
      -- `Commute` is just the symmetric form of the given equality.
      simpa [Commute, ContinuousLinearMap.star_eq_adjoint] using hTCLM.symm
    have hNormalCLM : IsStarNormal Tclm := hNormalCLM'

    -- Step 5: prove the spectrum of `Tclm` lives on the real axis.
    have hSpecReal : SpectrumRestricts Tclm Complex.reCLM := by
      -- Step 5.0: spectra of `T` and `Tclm` coincide via the algebra equivalence.
      have hSpecEq :
          spectrum ℂ Tclm = spectrum ℂ T :=
        AlgEquiv.spectrum_eq (Module.End.toContinuousLinearMap (𝕜 := ℂ) (E := V)) T
      -- Step 5.1: use the “all eigenvalues are real” hypothesis to show
      --           every spectral value comes from `ℝ`.
      refine SpectrumRestricts.of_subset_range_algebraMap (Complex.ofReal_re) ?subset
      intro z hz
      -- Step 5.1.1: reinterpret `hz` as a spectral point of `T`.
      have hzT : z ∈ spectrum ℂ T := by simpa [hSpecEq] using hz
      -- Step 5.1.2: spectra = eigenvalues in finite dimension.
      have hzEigen : T.HasEigenvalue z :=
        (hasEigenvalue_iff_mem_spectrum).2 hzT
      -- Step 5.1.3: package as a bundled eigenvalue and apply `hReal`.
      have hzImZero : (z : ℂ).im = 0 :=
        hReal ⟨z, hzEigen⟩
      -- Step 5.1.4: exhibit `z` as coming from `ℝ` using the vanished imaginary part.
      refine ⟨z.re, ?_⟩
      apply Complex.ext
      · simp
      · simp [hzImZero]

    -- Step 6: functional calculus – normal + real spectrum ⇒ self-adjoint.
    have hSelfCLM : IsSelfAdjoint Tclm := by
      -- provide the normal instance to the typeclass search explicitly
      haveI : IsStarNormal Tclm := hNormalCLM
      -- `SpectrumRestricts` is a reducible alias of `QuasispectrumRestricts`,
      -- so we can reuse the general functional-calculus lemma.
      exact QuasispectrumRestricts.isSelfAdjoint (a := Tclm) hSpecReal

    -- Step 7: transport self-adjointness back to linear maps.
    exact (LinearMap.isSelfAdjoint_toContinuousLinearMap_iff T).1 hSelfCLM
