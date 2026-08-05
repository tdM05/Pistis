import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Let $X$ be locally path connected. Show that every connected open set in $X$ is path connected.
-/

/-Informal Proof

Let $U$ be a open connected set in $X$. By Theorem 25.4, each path component of $U$ is open in $X$, hence open in $U$. Thus, each path component in $U$ is both open and closed in $U$, so must be empty or all of $U$. It follows that $U$ is path-connected.
-/

theorem Munkres_exercise_25_4 {X : Type*} [TopologicalSpace X]
  [LocPathConnectedSpace X] (U : Set X) (hU : IsOpen U)
  (hcU : IsConnected U) : IsPathConnected U := by
  -- Step 1: Retrieve the equivalence between connectedness and path connectedness for open subsets.
  have h_equiv : IsConnected U ↔ IsPathConnected U := by
    -- Step 1.1: Apply the dedicated mathlib lemma whose statement exactly matches the required equivalence.
    simpa using (IsOpen.isConnected_iff_isPathConnected hU)
  -- Step 2: Convert the provided connectedness hypothesis into path connectedness via the equivalence.
  -- Step 2.1: Use the forward implication of the equivalence obtained in Step 1 to reach the goal.
  exact (h_equiv).1 hcU
