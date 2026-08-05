import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Prove that every closed set in a separable metric space is the union of a (possibly empty) perfect set and a set which is at most countable.
-/

/-Informal Proof

If $E$ is closed, it contains all its limit points, and hence certainly all its condensation points. Thus $E=P \cup(E \backslash P)$, where $P$ is perfect (the set of all condensation points of $E$ ), and $E \backslash P$ is at most countable.

Since a perfect set in a separable metric space has the same cardinality as the real numbers, the set $P$ must be empty if $E$ is countable. The at-most countable set $E \backslash P$ cannot be perfect, hence must have isolated points if it is nonempty.
-/

theorem Rudin_exercise_2_28 (X : Type*) [MetricSpace X] [SeparableSpace X]
  (A : Set X) (hA : IsClosed A) :
  ∃ P₁ P₂ : Set X, A = P₁ ∪ P₂ ∧ Perfect P₁ ∧ Set.Countable P₂ := by
  -- Step 1: Switch to classical logic so that we can freely use choice when manipulating
  --         countable sets and perfect subsets.
  classical
  -- Step 2: Apply the Cantor–Bendixson theorem for closed sets inside second countable spaces.
  -- Step 2.1: Our separable metric hypotheses ensure `X` is second countable, so the theorem
  --           `exists_countable_union_perfect_of_isClosed` is available.
  obtain ⟨P₂, P₁, hP₂count, hP₁perf, hdecomp⟩ :=
    exists_countable_union_perfect_of_isClosed (α := X) (C := A) hA
  -- Step 3: Repackage the decomposition so that the perfect component is listed first.
  refine ⟨P₁, P₂, ?_, hP₁perf, hP₂count⟩
  -- Step 3.1: Use the commutativity of union to match the order requested in the statement.
  simpa [Set.union_comm] using hdecomp
