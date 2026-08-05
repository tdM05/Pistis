import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators



/-Informal Statement

Suppose $V$ is a complex inner-product space. Prove that every normal operator on $V$ has a square root. (An operator $S \in \mathcal{L}(V)$ is called a square root of $T \in \mathcal{L}(V)$ if $S^{2}=T$.)
-/

/-Informal Proof

Let $V$ be a complex inner product space.
It is known that an operator $S \in \mathcal{L}(V)$ is called a square root of $T \in \mathcal{L}(V)$ if
$$
S^2=T
$$
Now, suppose that $T$ is a normal operator on $V$.
By the Complex Spectral Theorem, there is $e_1, \ldots, e_n$ an orthonormal basis of $V$ consisting of eigenvalues of $T$ and let $\lambda_1, \ldots, \lambda_n$ denote their corresponding eigenvalues.
Define $S$ by
$$
S e_j=\sqrt{\lambda_j} e_j,
$$
for each $j=1, \ldots, n$.
Obviously, $S^2 e_j=\lambda_j e_j=T e_j$.
Hence, $S^2=T$ so there exist a square root of $T$.
-/

theorem Axler_exercise_7_11 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] {T : End ℂ V} (hT : T*adjoint T = adjoint T*T) :
  ∃ (S : End ℂ V), S ^ 2 = T := by
  classical
  -- ###############################################################
  -- Step 0: Move to the continuous-linear world, where the C⋆-algebra
  --         structure (and functional calculus) is available.
  -- ###############################################################
  haveI := FiniteDimensional.complete ℂ V
  -- Step 0.1: Regard `T` as a continuous linear map.
  let Tclm : V →L[ℂ] V := LinearMap.toContinuousLinearMap T
  -- Step 0.2: Transport the “normal” identity to the continuous side.
  have hTCLM : Tclm * Tclm.adjoint = Tclm.adjoint * Tclm := by
    -- Step 0.2.1: Push the equality through the algebra equivalence.
    have hRaw :
        Tclm * (LinearMap.toContinuousLinearMap (adjoint T)) =
          LinearMap.toContinuousLinearMap (adjoint T) * Tclm := by
      simpa using
        (congrArg (Module.End.toContinuousLinearMap (𝕜 := ℂ) (E := V)) hT)
    -- Step 0.2.2: Identify the adjoint on both sides.
    have hAdj :
        LinearMap.toContinuousLinearMap (adjoint T) = Tclm.adjoint := by
      simpa [Tclm] using (LinearMap.adjoint_toContinuousLinearMap T)
    -- Step 0.2.3: Rewrite using the adjoint identification.
    simpa [hAdj] using hRaw
  -- Step 0.3: Register normality as a typeclass instance for `Tclm`.
  have hNormal : IsStarNormal Tclm :=
    (isStarNormal_iff (x := Tclm)).2 (by
      -- `Commute (star Tclm) Tclm` is equivalent to the given identity.
      simpa [ContinuousLinearMap.star_eq_adjoint, Commute] using hTCLM.symm)
  -- Step 0.4: Make the functional-calculus typeclass instance explicit for clarity.
  haveI : ContinuousFunctionalCalculus ℂ (V →L[ℂ] V) IsStarNormal :=
    (IsStarNormal.instContinuousFunctionalCalculus (A := V →L[ℂ] V))

  -- ###############################################################
  -- Step 1: Record that the spectrum of `Tclm` is finite and identify
  --         it with the spectrum of the original linear map `T`.
  -- ###############################################################
  -- Step 1.1: Spectra coincide under the algebra equivalence.
  have hSpecEq : spectrum ℂ Tclm = spectrum ℂ T :=
    AlgEquiv.spectrum_eq (Module.End.toContinuousLinearMap (𝕜 := ℂ) (E := V)) T
  -- Step 1.2: The spectrum is finite because the space is finite dimensional.
  have hSpecFinite : (spectrum ℂ Tclm).Finite := by
    simpa [hSpecEq] using (Module.End.finite_spectrum (V := V) (K := ℂ) T)

  -- ###############################################################
  -- Step 2: Choose, pointwise on the spectrum, an arbitrary square
  --         root for each spectral value.
  -- ###############################################################
  -- Step 2.1: On the spectrum viewed as a subtype, pick a square root.
  let sqrtSpec : spectrum ℂ Tclm → ℂ :=
    fun z => Classical.choose (IsAlgClosed.exists_eq_mul_self (z : ℂ))
  -- Step 2.2: Record the square property of the chosen roots.
  have h_sqrtSpec_sq : ∀ z : spectrum ℂ Tclm, sqrtSpec z * sqrtSpec z = z := by
    intro z
    -- `choose` gives `(z : ℂ) = w * w`; flip the equality for convenience.
    have h := Classical.choose_spec (IsAlgClosed.exists_eq_mul_self (z : ℂ))
    -- `h` has shape `(z : ℂ) = w * w`; rearrange to the required form.
    simpa [sqrtSpec, mul_comm] using h.symm

  -- ###############################################################
  -- Step 3: Extend these pointwise choices to a global function
  --         `f : ℂ → ℂ` that agrees with the chosen roots on the
  --         spectrum. Continuity on the spectrum is automatic because
  --         the spectrum is finite (T1 + finite set ⇒ every function
  --         is continuous on that set).
  -- ###############################################################
  let f : ℂ → ℂ := fun z =>
    if hz : z ∈ spectrum ℂ Tclm then sqrtSpec ⟨z, hz⟩ else 0
  -- Step 3.1: Continuity of `f` on the (finite) spectrum.
  have h_cont : ContinuousOn f (spectrum ℂ Tclm) :=
    hSpecFinite.continuousOn f
  -- Step 3.2: On the spectrum, the function squares back to the identity.
  have h_square_on : (spectrum ℂ Tclm).EqOn (fun z => f z * f z) (fun z => z) := by
    intro z hz
    -- Reduce using the definition of `f` on spectral points.
    simp [f, hz, h_sqrtSpec_sq]  -- the `if_pos` branch triggers, giving `√z ^2 = z`.

  -- ###############################################################
  -- Step 4: Apply the continuous functional calculus to turn `f` into
  --         an operator `Sclm`, then compute `Sclm * Sclm = Tclm` by
  --         combining multiplicativity with the equality-on-spectrum
  --         fact established above.
  -- ###############################################################
  -- Step 4.1: Functional calculus image of `f`.
  set Sclm : V →L[ℂ] V := cfc (R := ℂ) (p := IsStarNormal) f Tclm
  -- Step 4.2: Use multiplicativity to express `Sclm^2` via `f^2`.
  have h_mul : cfc (R := ℂ) (p := IsStarNormal) (fun z => f z * f z) Tclm =
      Sclm * Sclm := by
    -- `cfc_mul` gives the needed multiplicativity.
    simpa [Sclm] using
      (cfc_mul (R := ℂ) (A := V →L[ℂ] V) (p := IsStarNormal)
        f f Tclm h_cont h_cont)
  -- Step 4.3: Replace `f^2` by the identity on the spectrum.
  have h_to_id : cfc (R := ℂ) (p := IsStarNormal) (fun z => f z * f z) Tclm =
      cfc (R := ℂ) (p := IsStarNormal) (fun z => z) Tclm := by
    -- Ensure the functional-calculus instance is in scope for this block.
    haveI := (inferInstance : ContinuousFunctionalCalculus ℂ (V →L[ℂ] V) IsStarNormal)
    -- Step 4.3.1: Continuity of the squared function on the spectrum.
    have h_cont_sq : ContinuousOn (fun z => f z * f z) (spectrum ℂ Tclm) :=
      h_cont.mul h_cont
    -- Step 4.3.2: Continuity of the identity function on the spectrum.
    have h_id_cont : ContinuousOn (fun z => z) (spectrum ℂ Tclm) := by
      -- the identity is continuous everywhere, hence on the spectrum.
      exact (continuous_id.continuousOn)
    -- `cfc_eq_cfc_iff_eqOn` converts pointwise equality on the spectrum.
    exact (cfc_eq_cfc_iff_eqOn (R := ℂ) (A := V →L[ℂ] V)
      (p := IsStarNormal) (a := Tclm)
      (f := fun z => f z * f z) (g := fun z => z)
      (ha := hNormal) (hf := h_cont_sq) (hg := h_id_cont)).2 h_square_on
  -- Step 4.4: Bundle the previous steps to obtain `Sclm * Sclm = Tclm`.
  have h_sq_clm : Sclm * Sclm = Tclm := by
    -- chain the equalities and finish with `cfc_id'`.
    calc
      Sclm * Sclm = cfc (R := ℂ) (p := IsStarNormal) (fun z => f z * f z) Tclm := h_mul.symm
      _ = cfc (R := ℂ) (p := IsStarNormal) (fun z => z) Tclm := h_to_id
      _ = Tclm := cfc_id' (R := ℂ) (p := IsStarNormal) (a := Tclm) hNormal

  -- ###############################################################
  -- Step 5: Transport the result back to plain linear maps (`End ℂ V`).
  -- ###############################################################
  -- Step 5.1: Algebra equivalence between linear and continuous-linear maps.
  let φ := Module.End.toContinuousLinearMap (𝕜 := ℂ) (E := V)
  -- Step 5.2: Define the desired linear map as the inverse image of `Sclm`.
  let S : End ℂ V := φ.symm Sclm
  -- Step 5.3: Convert the equality `Sclm * Sclm = Tclm` back through `φ`.
  have h_sq_end : S * S = T := by
    -- Apply `φ.symm` (an algebra equivalence) to both sides of `h_sq_clm`.
    have := congrArg φ.symm h_sq_clm
    -- Rewrite using multiplicativity of `φ.symm` and its action on `Tclm`.
    simpa [S, Tclm, map_mul] using this
  -- Step 5.4: Conclude with the requested square-root witness.
  refine ⟨S, ?_⟩
  -- `pow_two` turns the goal `S ^ 2 = T` into `S * S = T`.
  simpa [S, pow_two] using h_sq_end
