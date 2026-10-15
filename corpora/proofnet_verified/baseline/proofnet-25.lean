import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators ComplexOrder



/-Informal Statement

Prove that if $T \in \mathcal{L}(V)$ is normal, then $\operatorname{range} T=\operatorname{range} T^{*}.$
-/

/-Informal Proof

Let $T \in \mathcal{L}(V)$ to be a normal operator.
Suppose $u \in \operatorname{null} T$. Then, by $7.20$,
$$
0=\|T u\|=\left\|T^* u\right\|,
$$
which implies that $u \in \operatorname{null} T^*$.
Hence
$$
\operatorname{null} T=\operatorname{null} T^*
$$
because $\left(T^*\right)^*=T$ and the same argument can be repeated.
Now we have
$$
\begin{aligned}
\text { range } T & =\left(\text { null } T^*\right)^{\perp} \\
& =(\text { null } T)^{\perp} \\
& =\operatorname{range} T^*,
\end{aligned}
$$
where the first and last equality follow from items (d) and (b) of 7.7.
Hence, range $T=$ range $T^*$.
-/

theorem Axler_exercise_7_6 {V : Type*} [NormedAddCommGroup V] [RCLike F] [InnerProductSpace F V]
  [FiniteDimensional F V] (T : End F V)
  (hT : T * adjoint T = adjoint T * T) :
  range T = range (adjoint T) := by
  classical
  haveI := FiniteDimensional.complete F V
  -- Step 1: Transfer the normality relation to continuous linear maps.
  let Tclm : V →L[F] V := LinearMap.toContinuousLinearMap T
  have hTCLM :
      Tclm * Tclm.adjoint = Tclm.adjoint * Tclm := by
    -- Step 1.1: Apply the algebra equivalence between endomorphisms and continuous maps.
    have hRaw :
        Tclm * (LinearMap.toContinuousLinearMap (adjoint T)) =
          LinearMap.toContinuousLinearMap (adjoint T) * Tclm := by
      -- Using the multiplicativity of the equivalence.
      simpa using
        (congrArg (Module.End.toContinuousLinearMap (𝕜 := F) (E := V)) hT)
    -- Step 1.2: Identify the adjoint on both sides of the equality.
    have hAdj :
        LinearMap.toContinuousLinearMap (adjoint T) = Tclm.adjoint := by
      simpa [Tclm] using (LinearMap.adjoint_toContinuousLinearMap T)
    -- Step 1.3: Substitute the adjoint description using congruence.
    have hLeft :
        Tclm * Tclm.adjoint =
          Tclm * LinearMap.toContinuousLinearMap (adjoint T) :=
      by simpa using congrArg (fun f => Tclm * f) hAdj.symm
    have hRight :
        LinearMap.toContinuousLinearMap (adjoint T) * Tclm =
          Tclm.adjoint * Tclm :=
      by simpa using congrArg (fun f => f * Tclm) hAdj
    exact hLeft.trans (hRaw.trans hRight)
  -- Step 1.4: Record the continuous-linear-map description of the adjoint for later rewrites.
  have hAdjCLM :
      LinearMap.toContinuousLinearMap (adjoint T) = Tclm.adjoint := by
    simpa [Tclm] using (LinearMap.adjoint_toContinuousLinearMap T)
  have hAdjAdj :
      ((adjoint T).toContinuousLinearMap).adjoint =
        LinearMap.toContinuousLinearMap T := by
    simpa using
      (LinearMap.adjoint_toContinuousLinearMap (adjoint T)).symm
  -- Step 1.3: Record that the continuous operator is star normal.
  have hStarNormal : IsStarNormal Tclm := by
    -- The star on `Tclm` is its adjoint.
    refine ⟨?_⟩
    simpa [ContinuousLinearMap.star_eq_adjoint] using hTCLM.symm
  -- Step 1.4: Pull back the kernel equality to the original linear maps.
  have hKer :
      LinearMap.ker T = LinearMap.ker (adjoint T) := by
    -- Apply the continuous result and translate via the equivalence.
    have hKerCLM :=
      ContinuousLinearMap.IsStarNormal.ker_adjoint_eq_ker hStarNormal
    simpa [Tclm, LinearMap.coe_toContinuousLinearMap,
      LinearMap.adjoint_toContinuousLinearMap] using hKerCLM.symm
  -- Step 2: Express the ranges as orthogonal complements.
  have hRangeOrth :
      (LinearMap.range T)ᗮ = LinearMap.ker (adjoint T) := by
    -- Step 2.1.1: Invoke the continuous-linear-map version and translate back to linear maps.
    simpa [LinearMap.coe_toContinuousLinearMap,
      LinearMap.adjoint_eq_toCLM_adjoint, Tclm] using
      (ContinuousLinearMap.orthogonal_range Tclm)
  -- Step 2.2: Express `range T†` as the orthogonal complement of `ker T`.
  have hRangeAdjOrth :
      (LinearMap.range (adjoint T))ᗮ = LinearMap.ker T := by
    -- Step 2.2.1: Apply the same lemma to `T†`.
    have hOrthAdj :=
      ContinuousLinearMap.orthogonal_range ((adjoint T).toContinuousLinearMap)
    have hOrthAdj' :
        (LinearMap.range (adjoint T))ᗮ =
          (((adjoint T).toContinuousLinearMap).adjoint).ker := by
      simpa [LinearMap.coe_toContinuousLinearMap, hAdjCLM]
        using hOrthAdj
    have hRight :
        (((adjoint T).toContinuousLinearMap).adjoint).ker =
          LinearMap.ker T := by
      simp [hAdjAdj]
    exact hOrthAdj'.trans hRight
  -- Step 3: Remove orthogonal complements to obtain direct descriptions of the ranges.
  have hRangeT :
      LinearMap.range T = (LinearMap.ker (adjoint T))ᗮ := by
    -- Step 3.1: Take orthogonal complements on both sides of the relation from Step 2.1.
    have hDouble :=
      congrArg Submodule.orthogonal hRangeOrth
    -- Step 3.2: Replace the double orthogonal with the original submodule using finite-dimensionality.
    have hSelf :
        LinearMap.range T = (LinearMap.range T)ᗮᗮ := by
      -- Step 3.2.1: Use the closure characterization together with finite-dimensional closedness.
      have hClosure :=
        (Submodule.topologicalClosure_eq_self
          (𝕜 := F) (E := V) (K := LinearMap.range T)).symm
      have hOrth :=
        (Submodule.orthogonal_orthogonal_eq_closure (LinearMap.range T)).symm
      exact hClosure.trans hOrth
    -- Step 3.3: Combine the previous equalities.
    exact hSelf.trans hDouble
  have hRangeAdj :
      LinearMap.range (adjoint T) = (LinearMap.ker T)ᗮ := by
    -- Step 3.4: Repeat the argument for `T†`.
    have hDouble :=
      congrArg Submodule.orthogonal hRangeAdjOrth
    -- Step 3.5: Replace the double orthogonal of the adjoint's range with itself.
    have hSelf :
        LinearMap.range (adjoint T) = (LinearMap.range (adjoint T))ᗮᗮ := by
      have hClosure :=
        (Submodule.topologicalClosure_eq_self
          (𝕜 := F) (E := V) (K := LinearMap.range (adjoint T))).symm
      have hOrth :=
        (Submodule.orthogonal_orthogonal_eq_closure
          (LinearMap.range (adjoint T))).symm
      exact hClosure.trans hOrth
    -- Step 3.6: Combine the equalities for the adjoint.
    exact hSelf.trans hDouble
  -- Step 4: Substitute the kernel equality to align both range descriptions.
  have hRangeT' :
      LinearMap.range T = (LinearMap.ker T)ᗮ := by
    -- Step 4.1: Replace `ker T†` with `ker T` in the description of `range T`.
    simpa [hKer.symm] using hRangeT
  -- Step 4.2: Combine the two equalities to obtain the final conclusion.
  exact hRangeT'.trans hRangeAdj.symm
