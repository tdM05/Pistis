import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Let $X$ be a topological space; let $A$ be a subset of $X$. Suppose that for each $x \in A$ there is an open set $U$ containing $x$ such that $U \subset A$. Show that $A$ is open in $X$.
-/

/-Informal Proof

Since, from the given hypothesis given any $x \in A$ there exists an open set containing $x$ say, $U_x$ such that $U_x \subset A$. Thus, we claim that
$$
A=\bigcup_{x \in A} U_x
$$
Observe that if we prove the above claim, then $A$ will be open, being a union of arbitrary open sets. Since, for each $x \in A, U_x \subset A \Longrightarrow \cup U_x \subset A$. For the converse, observe that given any $x \in A, x \in U_x$ and hence in the union. Thus we proved our claim, and hence $A$ is an open set.
-/

theorem Munkres_exercise_13_1 (X : Type*) [TopologicalSpace X] (A : Set X)
  (h1 : ∀ x ∈ A, ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ U ⊆ A) :
  IsOpen A := by
  -- Step 1: Observe that the hypothesis `h1` matches the standard openness criterion.
  -- Step 1.1: The lemma `isOpen_iff_forall_mem_open` states that a set is open iff each of its points
  --           has an open neighborhood contained in the set; this is precisely the structure present in `h1`.
  -- Step 2: Apply the lemma to reduce the goal to providing, for any `x ∈ A`, an open subset of `A` containing `x`.
  refine isOpen_iff_forall_mem_open.mpr ?_ 
  -- Step 2.1: Fix an arbitrary point `x ∈ A` and unpack the data provided by `h1` for this point.
  intro x hx
  -- Step 2.2: Extract from `h1` an open neighborhood `U` with `x ∈ U` and `U ⊆ A`.
  rcases h1 x hx with ⟨U, hxU, hU_open, hU_subsetA⟩
  -- Step 2.3: Repackage the data so that it matches the tuple required by `isOpen_iff_forall_mem_open`.
  refine ⟨U, ?_⟩
  -- Step 2.3.1: Provide the inclusion `U ⊆ A` along with the remaining openness and membership data.
  refine ⟨hU_subsetA, ?_⟩
  -- Step 2.3.2: Confirm that `U` is open and contains the point `x`.
  exact ⟨hU_open, hxU⟩
