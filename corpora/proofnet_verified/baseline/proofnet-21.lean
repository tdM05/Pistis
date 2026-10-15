import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators



/-Informal Statement

Suppose that $T \in \mathcal{L}(V)$ has $\operatorname{dim} V$ distinct eigenvalues and that $S \in \mathcal{L}(V)$ has the same eigenvectors as $T$ (not necessarily with the same eigenvalues). Prove that $S T=T S$.
-/

/-Informal Proof

First off, let $n=\operatorname{dim} V$. so, there is a basis of $\left(v_1, \ldots, v_j\right)$ of $V$ that consist of eigenvectors of $T$. Now, let $\lambda_1, \ldots, \lambda_n$ be the corresponding eigenvalues, then we would have $T v_j=\lambda_1 v_j$ for every single $j$.

Now, for every $v_j$ is also an eigenvector of S, so $S v_j=a_j v_j$ for some $a_j \in F$. For each $j$, we would then have $(S T) v_j=S\left(T v_j\right)=\lambda_j S v_j=a_j \lambda_j v_j$ and $(T S) v_j=T\left(S v_j\right)=a_j T v_j=a_j \lambda_j v_j$. Since both operators, which are $S T$ and $T S$, agree on a basis, then both are equal.
-/

theorem Axler_exercise_5_20 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] [FiniteDimensional F V] {S T : End F V}
  (h1 : card (T.Eigenvalues) = finrank F V)
  (h2 : ∀ v : V, (∃ c : F, v ∈ eigenspace S c) ↔ (∃ c : F, v ∈ eigenspace T c)) :
  S * T = T * S := by
  classical
  -- Step 1: For every eigenvalue of `T`, pick a corresponding nonzero eigenvector.
  have h_exists :
      ∀ l : T.Eigenvalues, ∃ v : V, T.HasEigenvector (l : F) v := by
    intro l
    exact Module.End.HasEigenvalue.exists_hasEigenvector (f := T) (μ := (l : F)) l.property
  -- Step 1.1: Use the axiom of choice to obtain a concrete eigenvector for each eigenvalue.
  choose eigenvec h_eigenvec using h_exists
  -- Step 2: The chosen eigenvectors form a linearly independent family because their eigenvalues are distinct.
  have h_linearIndependent :
      LinearIndependent F fun l : T.Eigenvalues ↦ eigenvec l :=
    T.eigenvectors_linearIndependent' (fun l : T.Eigenvalues ↦ (l : F)) Subtype.coe_injective
      (fun l ↦ eigenvec l) (fun l ↦ h_eigenvec l)
  -- Step 3: This linearly independent family has as many elements as the dimension of `V`,
  --         hence it spans the whole space.
  have h_span :
      Submodule.span F (Set.range fun l : T.Eigenvalues ↦ eigenvec l) = ⊤ := by
    -- Step 3.1: Convert the cardinality hypothesis to the language expected by the lemma.
    have h_card : Fintype.card T.Eigenvalues = finrank F V := by
      simpa using h1
    -- Step 3.2: Apply the spanning lemma for a linearly independent family of maximal size.
    exact
      LinearIndependent.span_eq_top_of_card_eq_finrank' h_linearIndependent h_card
  -- Step 4: Show that `(S * T) - (T * S)` annihilates every chosen eigenvector.
  have h_comm_on_basis :
      ∀ l : T.Eigenvalues, ((S * T) - (T * S)) (eigenvec l) = 0 := by
    intro l
    -- Step 4.1: Record the eigenvector equation for `T`.
    have h_T_apply : T (eigenvec l) = (l : F) • eigenvec l :=
      (Module.End.HasEigenvector.apply_eq_smul (h_eigenvec l))
    -- Step 4.2: Use the hypothesis that eigenvectors of `T` are also eigenvectors of `S`.
    have h_mem_T : eigenvec l ∈ eigenspace T (l : F) :=
      (Module.End.hasEigenvector_iff.mp (h_eigenvec l)).1
    have h_mem_S :
        ∃ μ : F, eigenvec l ∈ eigenspace S μ :=
      (h2 (eigenvec l)).mpr ⟨(l : F), h_mem_T⟩
    -- Step 4.3: Pick the corresponding eigenvalue `μ` for `S` and write down the eigenvector equation.
    obtain ⟨μ, h_S_mem⟩ := h_mem_S
    have h_S_apply : S (eigenvec l) = μ • eigenvec l :=
      (mem_eigenspace_iff).1 h_S_mem
    -- Step 4.4: Compute the commutator `(S * T) - (T * S)` on `eigenvec λ`.
    --           Both sides act by successive scalar multiplications, so the difference is zero.
    have h_ST :
        (S * T) (eigenvec l) = ((l : F) * μ) • eigenvec l := by
      -- Step 4.4.1: Apply `S` to the scalar multiple produced by `T`.
      simp [Module.End.mul_apply, h_T_apply, h_S_apply, smul_smul]
    have h_TS :
        (T * S) (eigenvec l) = (μ * (l : F)) • eigenvec l := by
      -- Step 4.4.2: Apply `T` to the scalar multiple produced by `S`.
      simp [Module.End.mul_apply, h_T_apply, h_S_apply, smul_smul]
    -- Step 4.4.3: Subtract the two expressions; the scalars coincide, so the result is zero.
    simp [LinearMap.sub_apply, h_ST, h_TS, mul_comm]
  -- Step 5: The commutator vanishes on the span of the eigenvectors, hence on the whole space.
  have h_span_le :
      Submodule.span F (Set.range fun l : T.Eigenvalues ↦ eigenvec l) ≤
        LinearMap.ker ((S * T) - (T * S)) := by
    -- Step 5.1: A linear map that is zero on generators is zero on the span.
    refine Submodule.span_le.mpr ?_
    -- Step 5.2: Every generator is of the form `eigenvec λ`.
    rintro x ⟨l, rfl⟩
    -- Step 5.3: Translate the vanishing equation into membership in the kernel.
    simpa [LinearMap.mem_ker] using h_comm_on_basis l
  -- Step 5.4: Combine the previous steps to see that every vector lies in the kernel.
  have h_top_le :
      (⊤ : Submodule F V) ≤ LinearMap.ker ((S * T) - (T * S)) := by
    simpa [h_span] using h_span_le
  -- Step 5.5: Conclude that the commutator is the zero map.
  have h_zero :
      (S * T) - (T * S) = 0 := by
    ext v
    -- Step 5.5.1: Every `v` belongs to the kernel because the kernel contains `⊤`.
    have hv : v ∈ LinearMap.ker ((S * T) - (T * S)) :=
      h_top_le (by simp)
    -- Step 5.5.2: Translate kernel membership back to the defining equality.
    simpa [LinearMap.mem_ker] using hv
  -- Step 6: Reinterpret the vanishing commutator as the desired commutativity statement.
  simpa using sub_eq_zero.mp h_zero
