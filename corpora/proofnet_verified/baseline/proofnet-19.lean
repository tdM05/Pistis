import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators



/-Informal Statement

Suppose that $S, T \in \mathcal{L}(V)$ are such that $S T=T S$. Prove that $\operatorname{null} (T-\lambda I)$ is invariant under $S$ for every $\lambda \in \mathbf{F}$.
-/

/-Informal Proof

First off, fix $\lambda \in F$. Secondly, let $v \in \operatorname{null}(T-\lambda I)$. If so, then $(T-\lambda I)(S v)=T S v-\lambda S v=$ $S T v-\lambda S v=S(T v-\lambda v)=0$. Therefore, $S v \in \operatorname{null}(T-\lambda I)$ since $n u l l(T-\lambda I)$ is actually invariant under $S$.
-/

theorem Axler_exercise_5_4 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] (S T : V →ₗ[F] V) (hST : S ∘ T = T ∘ S) (c : F):
  Submodule.map S (ker (T - c • LinearMap.id)) = ker (T - c • LinearMap.id) := by
  sorry

/-
The universal equality asserted above fails: let the base field be ℚ, the vector space V be ℚ,
choose both S and T to be the zero linear endomorphism, and set c = 0. Then T - c • id equals 0,
whose kernel is all of V, while the image of that kernel through S collapses to {0}.
Thus the claimed equality cannot hold without extra hypotheses such as S being injective on the kernel.
-/

theorem Axler_exercise_5_4_neg :
  ∃ (F : Type) (V : Type) (_ : Field F) (_ : AddCommGroup V) (_ : Module F V)
    (S T : V →ₗ[F] V) (c : F),
      S ∘ T = T ∘ S ∧
        Submodule.map S (LinearMap.ker (T - c • LinearMap.id)) ≠
          LinearMap.ker (T - c • LinearMap.id) := by
  -- Step 1: Fix the counterexample data by working over the rational numbers.
  classical
  refine ⟨ℚ, ℚ, inferInstance, inferInstance, inferInstance, 0, 0, 0, ?_⟩
  -- Step 2: Verify that the chosen zero linear maps commute.
  constructor
  · -- Step 2.1: Two identically zero functions agree pointwise, so their compositions coincide.
    funext x
    -- Step 2.1.1: Evaluate both compositions on an arbitrary element to obtain 0.
    simp
  · -- Step 3: Assume equality of the mapped kernel and the kernel to derive a contradiction.
    intro hEq
    -- Step 3.1: Observe that 1 lies in the kernel of T - c • id for the chosen data.
    have h_one_mem :
        (1 : ℚ) ∈ LinearMap.ker ((0 : ℚ →ₗ[ℚ] ℚ) - 0 • LinearMap.id) := by
      -- Step 3.1.1: Evaluate the kernel predicate explicitly.
      simp
    -- Step 3.2: Transport the previous membership through the assumed equality.
    have h_one_in_image :
        (1 : ℚ) ∈
          Submodule.map (0 : ℚ →ₗ[ℚ] ℚ)
            (LinearMap.ker ((0 : ℚ →ₗ[ℚ] ℚ) - 0 • LinearMap.id)) := by
      -- Step 3.2.1: Use the submodule equality to transport membership.
      have hEq_mem :=
        congrArg (fun K : Submodule ℚ ℚ => (1 : ℚ) ∈ K) hEq
      -- Step 3.2.2: Apply the transported equality to the kernel membership.
      exact Eq.mpr hEq_mem h_one_mem
    -- Step 3.3: Unpack the definition of the mapped submodule to obtain an impossible equation.
    rcases h_one_in_image with ⟨x, _hx_mem, hx_eq⟩
    -- Step 3.3.1: The zero map applied to any input yields 0, contradicting hx_eq.
    simp at hx_eq

theorem Axler_exercise_5_4_corrected {F V : Type*} [AddCommGroup V] [Field F]
    [Module F V] (S T : V →ₗ[F] V) (hST : S ∘ T = T ∘ S) (c : F) :
    Submodule.map S (ker (T - c • LinearMap.id)) ≤ ker (T - c • LinearMap.id) := by
  -- Step 1: Pick an arbitrary element of the mapped kernel and show it lies in the kernel.
  intro y
  -- Step 1.1: Destructure the membership witness coming from the definition of Submodule.map.
  rintro ⟨x, hx_mem, rfl⟩
  -- Step 2: Translate the kernel condition into the equality T x = c • x.
  have hx_eq : T x = c • x := by
    -- Step 2.1: Evaluate the kernel predicate explicitly and solve for T x.
    simpa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero] using hx_mem
  -- Step 3: Use the commutation hypothesis to relate T (S x) and S (T x).
  have h_comm_pointwise :
      T (S x) = S (T x) := by
    -- Step 3.1: Apply the equality of compositions to x and rearrange.
    simpa using (congrArg (fun f => f x) hST).symm
  -- Step 4: Expand (T - c • id) (S x) and simplify the resulting expression.
  change T (S x) - c • S x = 0
  -- Step 4.1: Replace T (S x) with S (T x) via the commuting relation.
  have h_swap :
      T (S x) - c • S x =
        S (T x) - c • S x := by
    -- Step 4.1.1: Substitute the equality obtained in Step 3.
    simp [h_comm_pointwise]
  -- Step 4.2: Substitute the description of T x found in Step 2.
  have h_subst :
      S (T x) - c • S x =
        S (c • x) - c • S x := by
    -- Step 4.2.1: Replace T x with c • x.
    simp [hx_eq]
  -- Step 4.3: Evaluate S on the scalar multiple and cancel the resulting terms.
  have h_vanish :
      S (c • x) - c • S x = 0 := by
    -- Step 4.3.1: Linear maps respect scalar multiplication, so both terms coincide.
    simp
  -- Step 4.4: Chain the previous equalities to conclude the computation.
  have h_target :
      T (S x) - c • S x = 0 :=
    (h_swap.trans (h_subst.trans h_vanish))
  -- Step 4.5: Finish the proof by appealing to the computed equality.
  simpa using h_target
