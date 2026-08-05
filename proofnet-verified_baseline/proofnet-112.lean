import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Show that if $U$ is open in $X$ and $A$ is closed in $X$, then $U-A$ is open in $X$, and $A-U$ is closed in $X$.
-/

/-Informal Proof

Since
$$
X \backslash(U \backslash A)=(X \backslash U) \cup A \text { and } \quad X \backslash(A \backslash U)=(X \backslash A) \cup U,
$$
it follows that $X \backslash(U \backslash A)$ is closed in $X$ and $X \backslash(A \backslash U)$ is open in $X$.
-/

theorem Munkres_exercise_17_4 {X : Type*} [TopologicalSpace X]
  (U A : Set X) (hU : IsOpen U) (hA : IsClosed A) :
  IsOpen (U \ A) ∧ IsClosed (A \ U) := by
  classical
  -- Step 1: Prepare complements of the given sets so we can recast set differences as intersections.
  -- Step 1.1: Because A is closed, its complement Aᶜ is open; this will help with the openness of U \ A.
  have hAc_open : IsOpen (Aᶜ) := hA.isOpen_compl
  -- Step 1.2: Because U is open, its complement Uᶜ is closed; this will help with the closedness of A \ U.
  have hUc_closed : IsClosed (Uᶜ) := hU.isClosed_compl
  -- Step 2: Split the goal into proving both the openness of U \ A and the closedness of A \ U.
  constructor
  · -- Step 2.1: Recast U \ A as an intersection with the complement of A to leverage closure of open sets under intersection.
    have diff_UA_eq : U \ A = U ∩ Aᶜ := by
      -- Step 2.1.1: Establish set equality elementwise by unfolding membership in the difference and in the intersection.
      ext x
      -- Step 2.1.2: Forward direction—membership in the difference gives membership in U and non-membership in A.
      constructor <;> intro hx
      · -- Step 2.1.2.1: `hx.1` witnesses x ∈ U, while `hx.2` witnesses x ∉ A, i.e., x ∈ Aᶜ.
        exact ⟨hx.1, hx.2⟩
      · -- Step 2.1.2.2: Conversely, from x ∈ U ∩ Aᶜ we recover x ∈ U and x ∉ A, which is the definition of x ∈ U \ A.
        exact ⟨hx.1, hx.2⟩
    -- Step 2.2: Use the openness of U and Aᶜ to conclude the openness of their intersection, i.e., the difference.
    -- Step 2.2.1: Intersections of open sets are open, so U ∩ Aᶜ is open.
    have h_inter_open : IsOpen (U ∩ Aᶜ) := hU.inter hAc_open
    -- Step 2.2.2: Rewrite the target back to U \ A using the established equality.
    simpa [diff_UA_eq]
  · -- Step 2.3: Recast A \ U as an intersection with the complement of U to leverage closure of closed sets under intersection.
    have diff_AU_eq : A \ U = A ∩ Uᶜ := by
      -- Step 2.3.1: Establish the equality elementwise in the same manner as for the previous difference.
      ext x
      -- Step 2.3.2: Forward direction—membership in the difference provides x ∈ A together with x ∉ U.
      constructor <;> intro hx
      · -- Step 2.3.2.1: Package the witnesses into an intersection statement.
        exact ⟨hx.1, hx.2⟩
      · -- Step 2.3.2.2: Unpack the intersection statement to recover the definition of membership in A \ U.
        exact ⟨hx.1, hx.2⟩
    -- Step 2.4: Use the closedness of A and Uᶜ to conclude the closedness of their intersection, i.e., the difference.
    -- Step 2.4.1: Intersections of closed sets are closed, so A ∩ Uᶜ is closed.
    have h_inter_closed : IsClosed (A ∩ Uᶜ) := hA.inter hUc_closed
    -- Step 2.4.2: Rewrite the target back to A \ U using the established equality.
    simpa [diff_AU_eq]
