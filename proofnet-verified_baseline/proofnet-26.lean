import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

/-Informal Statement

Suppose $V$ is a complex inner-product space and $T \in \mathcal{L}(V)$ is a normal operator such that $T^{9}=T^{8}$. Prove that $T$ is self-adjoint and $T^{2}=T$.
-/

/-Informal Proof

Based on the complex spectral theorem, there is an orthonormal basis of $\left(e_1, \ldots, e_n\right)$ of $V$ consisting of eigenvectors of $T$. Now, let $\lambda_1, \ldots, \lambda_n$ be the corresponding eigenvalues. Therefore,
$$
T e_1=\lambda_j e_j
$$
for $j=1 \ldots n$.

Next, by applying $T$ repeatedly to both sides of the equation above, we get $T^9 e_j=\left(\lambda_j\right)^9 e_j$ and rei =8ej. Thus $T^8 e_j=\left(\lambda_j\right)^8 e_j$, which implies that $\lambda_j$ equals 0 or 1 . In particular, all the eigenvalues of $T$ are real. This would then imply that $T$ is self-adjoint.

Now, by applying $T$ to both sides of the equation above, we get
$$
\begin{aligned}
T^2 e_j & =\left(\lambda_j\right)^2 e_j \\
& =\lambda_j e_j \\
& =T e_j
\end{aligned}
$$
which is where the second equality holds because $\lambda_j$ equals 0 or 1 . Because $T^2$ and $T$ agree on a basis, they must be equal.
-/

set_option maxHeartbeats 800000 in
theorem Axler_exercise_7_10 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] (T : End ℂ V)
  (hT : T * adjoint T = adjoint T * T) (hT1 : T^9 = T^8) :
  IsSelfAdjoint T ∧ T^2 = T := by
  classical
  -- Step 0: finite-dimensional inner product spaces are complete, needed for adjoints on CLMs.
  haveI := FiniteDimensional.complete ℂ V

  -- Step 1: move to continuous linear maps so that the star-algebra API is available.
  let Tclm : V →L[ℂ] V := LinearMap.toContinuousLinearMap T

  -- Step 1.1: transport the normality hypothesis to `Tclm`.
  have hTCLM : Tclm * Tclm.adjoint = Tclm.adjoint * Tclm := by
    -- Use the algebra equivalence between endomorphisms and continuous linear maps.
    have hRaw :
        Tclm * (LinearMap.toContinuousLinearMap (adjoint T)) =
          LinearMap.toContinuousLinearMap (adjoint T) * Tclm := by
      simpa using
        (congrArg (Module.End.toContinuousLinearMap (𝕜 := ℂ) (E := V)) hT)
    -- Identify the adjoint inside the continuous world.
    have hAdj :
        LinearMap.toContinuousLinearMap (adjoint T) = Tclm.adjoint := by
      simpa [Tclm] using (LinearMap.adjoint_toContinuousLinearMap T)
    -- Rewrite both sides using the identification above.
    have hLeft :
        Tclm * Tclm.adjoint =
          Tclm * LinearMap.toContinuousLinearMap (adjoint T) := by
      simp [hAdj]
    have hRight :
        LinearMap.toContinuousLinearMap (adjoint T) * Tclm =
          Tclm.adjoint * Tclm := by
      simp [hAdj]
    exact hLeft.trans (hRaw.trans hRight)

  -- Step 1.2: transport the power identity `T⁹ = T⁸` to the continuous setting.
  have hT1CLM : Tclm^9 = Tclm^8 := by
    simpa [Tclm] using
      (congrArg (Module.End.toContinuousLinearMap (𝕜 := ℂ) (E := V)) hT1)

  -- Step 2: introduce the "defect" from idempotency, S = T - T^2.
  set S : V →L[ℂ] V := Tclm - Tclm^2 with hSdef

  -- Step 3: show that `S` is normal (commutes with its adjoint).
  -- Step 3.1: record basic commutation facts between `Tclm` and its adjoint.
  have hComm_T_A : Commute Tclm Tclm.adjoint := by
    -- `Commute` is definitionally the same as the equality we already have.
    simpa [Commute] using hTCLM
  -- Step 3.2: lift commutation to the various powers that occur in `S` and `S†`.
  have hComm_T2_A : Commute (Tclm^2) Tclm.adjoint := (hComm_T_A.pow_left 2)
  have hComm_T_A2 : Commute Tclm (Tclm.adjoint^2) := (hComm_T_A.pow_right 2)
  have hComm_T2_A2 : Commute (Tclm^2) (Tclm.adjoint^2) :=
    (hComm_T2_A.pow_right 2)
  -- A handy rewrite for the adjoint of a square.
  have hAdjPow2 : (Tclm^2).adjoint = Tclm.adjoint^2 := by
    -- First compute the adjoint of the product `T * T` using `star_mul`.
    have hStar : (Tclm * Tclm).adjoint = Tclm.adjoint * Tclm.adjoint := by
      have h := (star_mul Tclm Tclm)
      simpa [ContinuousLinearMap.star_eq_adjoint] using h
    -- Then fold back the power notation on both sides.
    calc
      (Tclm^2).adjoint = (Tclm * Tclm).adjoint := by simp [pow_two]
      _ = Tclm.adjoint * Tclm.adjoint := hStar
      _ = Tclm.adjoint^2 := by simp [pow_two]
  -- Step 3.2.1: explicit expression for the adjoint of `S`.
  have hAdjS : S.adjoint = Tclm.adjoint - (Tclm^2).adjoint := by
    -- expand the adjoint over the subtraction.
    have h : (Tclm - Tclm^2).adjoint = Tclm.adjoint - (Tclm^2).adjoint := by
      simp
    simp [hSdef, h]
  -- Step 3.3: combine the commutation lemmas to obtain commutation for `S`.
  have hComm_left : Commute Tclm (Tclm.adjoint - Tclm.adjoint^2) :=
    Commute.sub_right hComm_T_A hComm_T_A2
  have hComm_right : Commute (Tclm^2) (Tclm.adjoint - Tclm.adjoint^2) :=
    Commute.sub_right hComm_T2_A hComm_T2_A2
  have hComm_S : Commute S S.adjoint := by
    -- First commute the raw expressions, then rewrite back to `S`.
    have hTmp : Commute (Tclm - Tclm^2) (Tclm.adjoint - Tclm.adjoint^2) :=
      Commute.sub_left hComm_left hComm_right
    simpa [hSdef, hAdjS, hAdjPow2] using hTmp
  -- Step 3.4: package commutation as star-normality of `S`.
  have hSnormal : IsStarNormal S := ⟨by
    -- `star S` is `S.adjoint`, so the previous commutation suffices.
    have hTmp := hComm_S.symm
    simpa [ContinuousLinearMap.star_eq_adjoint, Commute] using hTmp⟩

  -- Step 4: prove that `S⁸ = 0` using the hypothesis `T⁹ = T⁸`.
  -- Step 4.1: turn `T⁹ = T⁸` into the factorised form `T⁸ (T - 1) = 0`.
  have hFactor : Tclm^8 * (Tclm - 1) = 0 := by
    calc
      Tclm^8 * (Tclm - 1) = Tclm^9 - Tclm^8 := by
        simp [mul_sub, pow_succ]
      _ = 0 := by
        have hSub : Tclm^9 - Tclm^8 = 0 := sub_eq_zero.mpr hT1CLM
        simpa using hSub

  -- Step 4.2: note that `S = T * (1 - T)` and that these factors commute.
  have hCommFactor : Commute Tclm (1 - Tclm) := by
    change Tclm * (1 - Tclm) = (1 - Tclm) * Tclm
    simp [mul_sub, sub_mul]
  have hS_mul : S = Tclm * (1 - Tclm) := by
    simp [hSdef, mul_sub, pow_two]
  -- Step 4.3: compute `S⁸` as a product of powers of the two commuting factors.
  have hSPow : S^8 = Tclm^8 * (1 - Tclm)^8 := by
    have hPow := hCommFactor.mul_pow 8
    simpa [hS_mul] using hPow
  -- Step 4.4: derive directly that `T^8 (1 - T)^8 = 0` by a simple induction.
  have hFactorOne : Tclm^8 * (1 - Tclm) = 0 := by
    calc
      Tclm^8 * (1 - Tclm) = Tclm^8 - Tclm^9 := by simp [mul_sub, pow_succ]
      _ = 0 := by simp [hT1CLM]
  have hZeroPow : Tclm^8 * (1 - Tclm)^8 = 0 := by
    -- Auxiliary induction on the exponent of `(1 - T)`.
    have hInd : ∀ n : ℕ, 0 < n → Tclm^8 * (1 - Tclm)^n = 0 := by
      intro n hn
      induction n with
      | zero => cases hn
      | succ n ih =>
          cases n with
          | zero =>
              -- Base case n = 1.
              simpa using hFactorOne
          | succ n =>
              have ih' : Tclm^8 * (1 - Tclm)^(Nat.succ n) = 0 := ih (Nat.succ_pos _)
              calc
                Tclm^8 * (1 - Tclm)^(Nat.succ (Nat.succ n))
                    = (Tclm^8 * (1 - Tclm)^(Nat.succ n)) * (1 - Tclm) := by
                        simp [pow_succ, mul_assoc]
                _ = 0 := by simp [ih']
    have h8pos : 0 < (8 : ℕ) := by decide
    simpa using hInd 8 h8pos

  -- Step 4.5: assemble the pieces to conclude `S⁸ = 0`.
  have hS8 : S^8 = 0 := by
    calc
      S^8 = Tclm^8 * (1 - Tclm)^8 := hSPow
      _ = 0 := hZeroPow

  -- Step 5: a reusable lemma – a square-zero normal operator must be zero.
  have zero_of_square_zero : ∀ A : V →L[ℂ] V, IsStarNormal A → A^2 = 0 → A = 0 := by
    intro A hNorm hSq
    -- Step 5.1: `A^2 = 0` implies the range of `A` sits inside its kernel.
    let A' : V →ₗ[ℂ] V := A.toLinearMap
    have hRangeKer : LinearMap.range A' ≤ LinearMap.ker A' := by
      intro y hy
      rcases hy with ⟨x, rfl⟩
      have hSqApply := congrArg (fun f => f x) hSq
      simpa [pow_two, A'] using hSqApply
    -- Step 5.2: normality gives `(range A)ᗮ = ker A`.
    have hOrth := ContinuousLinearMap.IsStarNormal.orthogonal_range hNorm
    -- Step 5.3: vectors in the range are orthogonal to themselves, hence zero.
    have hZeroOnRange : ∀ y ∈ LinearMap.range A', y = (0 : V) := by
      intro y hy
      have hyKer : y ∈ LinearMap.ker A' := hRangeKer hy
      have hyOrth : y ∈ (LinearMap.range A')ᗮ := by
        rw [show LinearMap.range A' = A.range from rfl] at hy ⊢
        simpa [hOrth] using hyKer
      have hInner : inner (𝕜 := ℂ) y y = (0 : ℂ) := by
        have hOrthCond :=
          (Submodule.mem_orthogonal (K := LinearMap.range A') (v := y)).mp hyOrth
        have hyInner := hOrthCond y hy
        simpa using hyInner
      exact inner_self_eq_zero.mp hInner
    -- Step 5.4: zero range forces the operator itself to vanish.
    ext x
    have hxRange : A x ∈ LinearMap.range A' := ⟨x, rfl⟩
    simp [hZeroOnRange _ hxRange]

  -- Step 6: repeatedly halve the nilpotency degree to deduce `S = 0`.
  -- Step 6.1: `S⁴` is normal and square-zero.
  have hS4_normal : IsStarNormal (S^4) := by
    -- `star (S^4)` = `(star S)^4`, and powers preserve commutation.
    have hCommBase : Commute (star S) S := hSnormal.star_comm_self
    have hCommPow : Commute ((star S)^4) (S^4) := hCommBase.pow_pow 4 4
    exact ⟨by simpa [star_pow] using hCommPow⟩
  have hS4_sq : (S^4)^2 = 0 := by
    -- `S⁸ = 0` and `S⁸ = (S⁴)²`.
    have h' : S^(4 * 2) = 0 := by simpa using hS8
    simpa [pow_mul] using h'
  have hS4_zero : S^4 = 0 := zero_of_square_zero _ hS4_normal hS4_sq

  -- Step 6.2: the same argument for `S²`.
  have hS2_normal : IsStarNormal (S^2) := by
    have hCommBase : Commute (star S) S := hSnormal.star_comm_self
    have hCommPow : Commute ((star S)^2) (S^2) := hCommBase.pow_pow 2 2
    exact ⟨by simpa [star_pow] using hCommPow⟩
  have hS2_sq : (S^2)^2 = 0 := by
    have h' : S^(2 * 2) = 0 := by simpa using hS4_zero
    simpa [pow_mul] using h'
  have hS2_zero : S^2 = 0 := zero_of_square_zero _ hS2_normal hS2_sq

  -- Step 6.3: finally `S` itself must vanish, giving idempotence of `Tclm`.
  have hS_sq : S^2 = 0 := hS2_zero
  have hS_zero : S = 0 := zero_of_square_zero _ hSnormal hS_sq
  have hIdempCLM : Tclm^2 = Tclm := by
    have hEq : Tclm - Tclm^2 = 0 := by simpa [hSdef] using hS_zero
    have hEq' : Tclm = Tclm^2 := sub_eq_zero.mp hEq
    simpa using hEq'.symm

  -- Step 7: translate idempotence back to `T` and extract self-adjointness.
  have hIdemp : T^2 = T := by
    have hCLM := congrArg ContinuousLinearMap.toLinearMap hIdempCLM
    -- `pow_two` is compatible with both flavours of endomorphisms.
    simpa [Tclm, pow_two] using hCLM

  -- Step 7.1: idempotent + normal ⇒ self-adjoint for operators on a Hilbert space.
  have hIdempElem : IsIdempotentElem Tclm := by
    -- `IsIdempotentElem` is the definitional statement `T*T = T`.
    simpa [IsIdempotentElem, pow_two] using hIdempCLM
  have hNormalCLM : IsStarNormal Tclm := by
    refine ⟨?comm⟩
    simpa [ContinuousLinearMap.star_eq_adjoint, Commute] using hTCLM.symm
  have hSelfAdjointCLM : IsSelfAdjoint Tclm :=
    (ContinuousLinearMap.IsIdempotentElem.isSelfAdjoint_iff_isStarNormal hIdempElem).mpr
      hNormalCLM

  -- Step 7.2: push self-adjointness back to the linear map level.
  have hSelfAdjoint : IsSelfAdjoint T :=
    (LinearMap.isSelfAdjoint_toContinuousLinearMap_iff T).mp hSelfAdjointCLM

  -- Step 8: assemble the final result.
  exact ⟨hSelfAdjoint, hIdemp⟩
