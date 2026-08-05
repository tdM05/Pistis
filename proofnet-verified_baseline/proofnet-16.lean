import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators



/-Informal Statement

Prove that the intersection of any collection of subspaces of $V$ is a subspace of $V$.
-/

/-Informal Proof

Let $V_1, V_2, \ldots, V_n$ be subspaces of the vector space $V$ over the field $F$. We must show that their intersection $V_1 \cap V_2 \cap \ldots \cap V_n$ is also a subspace of $V$.

To begin, we observe that the additive identity $0$ of $V$ is in $V_1 \cap V_2 \cap \ldots \cap V_n$. This is because $0$ is in each subspace $V_i$, as they are subspaces and hence contain the additive identity.

Next, we show that the intersection of subspaces is closed under addition. Let $u$ and $v$ be vectors in $V_1 \cap V_2 \cap \ldots \cap V_n$. By definition, $u$ and $v$ belong to each of the subspaces $V_i$. Since each $V_i$ is a subspace and therefore closed under addition, it follows that $u+v$ belongs to each $V_i$. Thus, $u+v$ belongs to the intersection $V_1 \cap V_2 \cap \ldots \cap V_n$.

Finally, we show that the intersection of subspaces is closed under scalar multiplication. Let $a$ be a scalar in $F$ and let $v$ be a vector in $V_1 \cap V_2 \cap \ldots \cap V_n$. Since $v$ belongs to each $V_i$, we have $av$ belongs to each $V_i$ as well, as $V_i$ are subspaces and hence closed under scalar multiplication. Therefore, $av$ belongs to the intersection $V_1 \cap V_2 \cap \ldots \cap V_n$.

Thus, we have shown that $V_1 \cap V_2 \cap \ldots \cap V_n$ is a subspace of $V$.
-/

theorem Axler_exercise_1_8 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] {ι : Type*} (u : ι → Submodule F V) :
  ∃ U : Submodule F V, (⋂ (i : ι), (u i).carrier) = ↑U := by
  -- Step 1: Enable classical logic to use choice-dependent lemmas about indexed intersections.
  classical
  -- Step 2: Choose the canonical candidate submodule, namely the infimum over the family.
  refine ⟨⨅ i, u i, ?_⟩
  -- Step 3: Compare the set-theoretic intersection with the carrier of the infimum via extensionality.
  ext x
  -- Step 3.1: Prove that membership in the intersection implies membership in the infimum submodule.
  constructor
  · -- Step 3.1.1: Assume `x` lies in the intersection of the underlying sets of each submodule.
    intro hx
    -- Step 3.1.1.1: Expand the intersection membership into pointwise membership in each submodule.
    have hx_all_carrier : ∀ i : ι, x ∈ (u i).carrier := by
      -- Step 3.1.1.1.1: Use the elimination rule for indexed intersections of sets.
      exact Set.mem_iInter.mp hx
    -- Step 3.1.2: Convert the pointwise membership into membership in the infimum submodule.
    -- Step 3.1.2.1: First rephrase the carrier-style membership in terms of submodule membership.
    have hx_all : ∀ i : ι, x ∈ u i := by
      -- Step 3.1.2.1.1: Coercions identify `x ∈ u i` with membership in the underlying set.
      intro i
      simpa using hx_all_carrier i
    -- Step 3.1.2.2: `Submodule.mem_iInf` translates the universal property into infimum membership.
    exact (Submodule.mem_iInf u).mpr hx_all
  · -- Step 3.2: Assume `x` belongs to the infimum submodule and deduce membership in every component.
    intro hx
    -- Step 3.2.1: Unpack the infimum membership into pointwise membership in each submodule.
    have hx_all : ∀ i : ι, x ∈ u i := by
      -- Step 3.2.1.1: Apply the introduction rule for `mem_iInf` to obtain the universal condition.
      exact (Submodule.mem_iInf u).mp hx
    -- Step 3.2.2: Reassemble the pointwise membership into the set-theoretic intersection.
    -- Step 3.2.2.1: Translate the submodule membership back to carrier-style membership.
    have hx_all_carrier : ∀ i : ι, x ∈ (u i).carrier := by
      -- Step 3.2.2.1.1: Use coercion equality between submodule and carrier membership.
      intro i
      simpa using hx_all i
    -- Step 3.2.2.2: `Set.mem_iInter` packages the universal condition as intersection membership.
    exact Set.mem_iInter.mpr hx_all_carrier
