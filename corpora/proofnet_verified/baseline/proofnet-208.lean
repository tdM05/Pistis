import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators InnerProductSpace


/-Informal Statement

Show that if $\operatorname{dim} V \geq 2$, then the set of normal operators on $V$ is not a subspace of $\mathcal{L}(V)$.
-/

/-Informal Proof

First off, suppose that $\operatorname{dim} V \geq 2$. Next let $\left(e_1, \ldots, e_n\right)$ be an orthonormal basis of $V$. Now, define $S, T \in L(V)$ by both $S\left(a_1 e_1+\ldots+a_n e_n\right)=a_2 e_1-a_1 e_2$ and $T\left(a_1 e_1+\ldots+\right.$ $\left.a_n e_n\right)=a_2 e_1+a_1 e_2$. So, just by now doing a simple calculation verifies that $S^*\left(a_1 e_1+\right.$ $\left.\ldots+a_n e_n\right)=-a_2 e_1+a_1 e_2$

Now, based on this formula, another calculation would show that $S S^*=S^* S$. Another simple calculation would that that $T$ is self-adjoint. Therefore, both $S$ and $T$ are normal. However, $S+T$ is given by the formula of $(S+T)\left(a_1 e_1+\ldots+a_n e_n\right)=2 a_2 e_1$. In this case, a simple calculator verifies that $(S+T)^*\left(a_1 e_1+\ldots+a_n e_n\right)=2 a_1 e_2$.

Therefore, there is a final simple calculation that shows that $(S+T)(S+T)^* \neq(S+$ $T)^*(S+T)$. So, in other words, $S+T$ isn't normal. Therefore, the set of normal operators on $V$ isn't closed under addition and hence isn't a subspace of $L(V)$.
-/

theorem Axler_exercise_7_5 {V : Type*} [NormedAddCommGroup V] [RCLike F] [InnerProductSpace F V]
  [FiniteDimensional F V] (hV : finrank F V ≥ 2) :
  ∀ U : Submodule F (End F V), U.carrier ≠
  {T | T * adjoint T = adjoint T * T} := by
  /- #####################################################################
      Step 0.  Set up notation and pick two orthonormal vectors.
      We rely on the canonical orthonormal basis provided by mathlib
      for finite-dimensional inner product spaces (`stdOrthonormalBasis`).
  ##################################################################### -/
  classical
  -- Step 0.0: rewrite the finrank bound with the scalar field made explicit
  -- Step 0.1: choose the standard orthonormal basis indexed by `Fin (finrank F V)`
  let e : OrthonormalBasis (Fin (finrank F V)) F V := stdOrthonormalBasis F V
  -- Step 0.2: manufacture the indices 0 and 1 using `hV : finrank V ≥ 2`
  have h0 : 0 < finrank F V := lt_of_lt_of_le (by decide : 0 < 2) hV
  have h1 : 1 < finrank F V := lt_of_lt_of_le (by decide : 1 < 2) hV
  let i0 : Fin (finrank F V) := ⟨0, h0⟩
  let i1 : Fin (finrank F V) := ⟨1, h1⟩
  -- Step 0.3: define the two orthonormal vectors we will work with
  let v₁ := e i0
  let v₂ := e i1
  have hOrth : Orthonormal F (fun i => e i) := e.orthonormal
  -- Step 0.4: record the basic orthonormal identities we will use repeatedly
  have hv12 : ⟪v₁, v₂⟫_F = 0 := by
    have hne_nat : (i0 : ℕ) ≠ (i1 : ℕ) := by
      have : (0 : ℕ) ≠ 1 := by decide
      simp [i0, i1]
    have hne : (i0 : Fin (finrank F V)) ≠ i1 := by
      intro h; apply hne_nat; exact congrArg Fin.val h
    exact hOrth.inner_eq_zero hne
  have hv11 : ⟪v₁, v₁⟫_F = 1 := by
    have hnorm : ‖v₁‖ = (1 : ℝ) := hOrth.norm_eq_one i0
    calc
      ⟪v₁, v₁⟫_F = (‖v₁‖ ^ 2 : F) := by simp [inner_self_eq_norm_sq_to_K]
      _ = (1 : F) := by simp [hnorm]
  have hv22 : ⟪v₂, v₂⟫_F = 1 := by
    have hnorm : ‖v₂‖ = (1 : ℝ) := hOrth.norm_eq_one i1
    calc
      ⟪v₂, v₂⟫_F = (‖v₂‖ ^ 2 : F) := by simp [inner_self_eq_norm_sq_to_K]
      _ = (1 : F) := by simp [hnorm]
  have hv21 : ⟪v₂, v₁⟫_F = 0 := by
    have hne_nat : (i1 : ℕ) ≠ (i0 : ℕ) := by
      have : (1 : ℕ) ≠ 0 := by decide
      simp [i0, i1]
    have hne : (i1 : Fin (finrank F V)) ≠ i0 := by
      intro h
      apply hne_nat
      simp [congrArg Fin.val h]
    exact hOrth.inner_eq_zero hne
  have hv₁_ne : v₁ ≠ 0 := by
    intro h
    have hnorm : ‖v₁‖ = (1 : ℝ) := hOrth.norm_eq_one i0
    have hz : ‖v₁‖ = 0 := by
      simp [h]
    linarith

  /- #####################################################################
      Step 1.  Define the rank‑one operators A(x)=⟪x,v₂⟫·v₁ and
      B(x)=⟪x,v₁⟫·v₂ together with the combinations S, T, N.
  ##################################################################### -/
  -- Step 1.1: a helper definition for the rank‑one map x ↦ ⟪x,w⟫ • v
  let rankOne : V → V → End F V :=
    fun v w =>
      { toFun := fun x => ⟪w, x⟫_F • v
        map_add' := by
          intro x y; simp [inner_add_right, add_smul]
        map_smul' := by
          intro a x; simp [inner_smul_right, smul_smul] }
  -- Step 1.2: instantiate the concrete operators A and B
  let A : End F V := rankOne v₁ v₂
  let B : End F V := rankOne v₂ v₁
  -- Step 1.3: skew/self adjoint combinations and their sum
  let S : End F V := A - B
  let T : End F V := A + B
  let N : End F V := S + T   -- this is the candidate that will fail to be normal

  /- #####################################################################
      Step 2.  Compute adjoints of the rank‑one maps and of S,T,N.
  ##################################################################### -/
  -- Step 2.1: the adjoint of a rank‑one map swaps the two vectors
  have hAdj_rankOne (v w : V) :
      rankOne w v = adjoint (rankOne v w) := by
    refine (eq_adjoint_iff _ _).2 ?_
    intro x y
    -- explicit inner product computation for the adjoint identity
    simp [rankOne, inner_smul_left, inner_smul_right, inner_conj_symm, mul_comm]
  -- Step 2.2: specialised adjoint facts for A and B
  have hAdjA : adjoint A = B := by
    -- hAdj_rankOne v₁ v₂ : B = adjoint A
    simpa [A, B] using (hAdj_rankOne v₁ v₂).symm
  have hAdjB : adjoint B = A := by
    simpa [A, B] using (hAdj_rankOne v₂ v₁).symm
  -- Step 2.3: S is skew‑adjoint, T is self‑adjoint
  have hAdjS : adjoint S = -S := by
    calc
      adjoint S = adjoint A - adjoint B := by
        -- adjoint respects subtraction (star is additive)
        simp [S]
      _ = B - A := by simp [hAdjA, hAdjB]
      _ = -(A - B) := by abel
      _ = -S := by simp [S]
  have hAdjT : adjoint T = T := by
    calc
      adjoint T = adjoint A + adjoint B := by
        simp [T]
      _ = B + A := by simp [hAdjA, hAdjB]
      _ = A + B := by abel
      _ = T := rfl

  /- #####################################################################
      Step 3.  Deduce normality of S and T, and compute N and its adjoint.
  ##################################################################### -/
  -- Step 3.1: S is normal because it is skew‑adjoint
  have hS_normal : S * adjoint S = adjoint S * S := by
    simp [hAdjS] -- both sides reduce to -(S*S)
  -- Step 3.2: T is normal because it is self‑adjoint
  have hT_normal : T * adjoint T = adjoint T * T := by
    simp [hAdjT]
  -- Step 3.3: simplify N and adjoint N to bit0 forms for easy evaluation
  have hN_simp : N = A + A := by
    -- expand N = (A - B) + (A + B) and rearrange with commutativity
    calc
      N = (A - B) + (A + B) := rfl
      _ = (A + A) + (B - B) := by abel
      _ = A + A := by abel
  have hAdjN_simp : adjoint N = B + B := by
    calc
      adjoint N = adjoint (A + A) := by simp [hN_simp]
      _ = adjoint A + adjoint A := by
        simp
      _ = B + B := by simp [hAdjA]

  /- #####################################################################
      Step 4.  Show N is *not* normal by evaluating on v₁.
  ##################################################################### -/
  -- Step 4.1: quick evaluations of A and B on v₁
  have hAv₁ : A v₁ = 0 := by simp [A, rankOne, hv21]
  have hBv₁ : B v₁ = v₂ := by
    have hn1 : ‖v₁‖ = 1 := hOrth.norm_eq_one i0
    simp [B, rankOne, hn1]
  -- Step 4.2: evaluate N and adjoint N on v₁
  have hNv₁ : N v₁ = 0 := by simp [hN_simp, hAv₁]
  have hAdjNv₁ : adjoint N v₁ = (2 : F) • v₂ := by
    calc
      adjoint N v₁ = B v₁ + B v₁ := by
        simp [hAdjN_simp]
      _ = v₂ + v₂ := by simp [hBv₁]
      _ = (2 : F) • v₂ := by simp [two_smul]
  -- Step 4.3: compute (N ∘ N†) v₁ and (N† ∘ N) v₁ explicitly
  have hLeft : (N * adjoint N) v₁ = (4 : F) • v₁ := by
    calc
      (N * adjoint N) v₁ = N (adjoint N v₁) := rfl
      _ = N ((2 : F) • v₂) := by simp [hAdjNv₁]
      _ = (A + A) ((2 : F) • v₂) := by simp [hN_simp]
      _ = A ((2 : F) • v₂) + A ((2 : F) • v₂) := rfl
      _ = (2 : F) • (A v₂) + (2 : F) • (A v₂) := by simp
      _ = (2 : F) • v₁ + (2 : F) • v₁ := by
        have hn2 : ‖v₂‖ = 1 := hOrth.norm_eq_one i1
        simp [A, rankOne, hn2]
      _ = (2 : F) • (v₁ + v₁) := by simp [smul_add]
      _ = (2 : F) • ((2 : F) • v₁) := by simp [two_smul]
      _ = ((2 : F) * (2 : F)) • v₁ := by simp [smul_smul]
      _ = (4 : F) • v₁ := by norm_num
  have hRight : (adjoint N * N) v₁ = 0 := by
    -- because N v₁ = 0
    simp [Module.End.mul_apply, hNv₁]
  -- Step 4.4: conclude the compositions disagree, so N is not normal
  have hN_not_normal : N * adjoint N ≠ adjoint N * N := by
    intro hEq
    have hEq_vals : (N * adjoint N) v₁ = (adjoint N * N) v₁ :=
      congrArg (fun f => f v₁) hEq
    have h4 : (4 : F) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero 3)
    have hNonzero : (4 : F) • v₁ ≠ (0 : V) := smul_ne_zero h4 hv₁_ne
    -- rewrite the evaluated equality and contradict non‑zero vs zero
    have : (4 : F) • v₁ = (0 : V) := by simpa [hLeft, hRight] using hEq_vals
    exact hNonzero this

  /- #####################################################################
      Step 5.  Use S and T lying in any putative submodule of normal
      operators to derive a contradiction with N.
  ##################################################################### -/
  intro U hEq
  -- Step 5.2: reformulate the assumed equality as a pointwise membership equivalence
  have hEq_mem : ∀ X : End F V, (X ∈ U ↔ X * adjoint X = adjoint X * X) := by
    intro X
    change X ∈ U.carrier ↔ X * adjoint X = adjoint X * X
    -- First convert the carrier equality to a membership equivalence,
    -- then use the definition of the set-builder.
    have hmem_eq : X ∈ U.carrier ↔ X ∈ {T | T * adjoint T = adjoint T * T} :=
      Iff.of_eq (congrArg (fun s => X ∈ s) hEq)
    simpa using hmem_eq
  -- Step 5.3: S and T satisfy the normality condition, hence belong to U
  have hS_mem : S ∈ U := (hEq_mem S).2 hS_normal
  have hT_mem : T ∈ U := (hEq_mem T).2 hT_normal
  -- Step 5.3: closure of U under addition puts N inside U
  have hN_mem : N ∈ U := by
    change N ∈ U.carrier
    have : S + T ∈ U := U.add_mem hS_mem hT_mem
    simpa [N] using this
  -- Step 5.4: normality of N would follow from membership, contradicting the explicit computation
  have hN_eq : N * adjoint N = adjoint N * N := (hEq_mem N).1 hN_mem
  exact hN_not_normal hN_eq
