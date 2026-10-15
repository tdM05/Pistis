import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Prove that every compact metric space $K$ has a countable base.
-/

/-Informal Proof

$K$ can be covered by a finite union of neighborhoods of radius $1 / n$, and this shows that this implies that $K$ is separable.

It is not entirely obvious that a metric space with a countable base is separable. To prove this, let $\left\{V_n\right\}_{n=1}^{\infty}$ be a countable base, and let $x_n \in V_n$. The points $V_n$ must be dense in $X$. For if $G$ is any non-empty open set, then $G$ contains $V_n$ for some $n$, and hence $x_n \in G$. (Thus for a metric space, having a countable base and being separable are equivalent.)
-/

theorem Rudin_exercise_2_25 {K : Type*} [MetricSpace K] [CompactSpace K] :
  ∃ (B : Set (Set K)), Set.Countable B ∧ IsTopologicalBasis B := by
  classical
  -- Step 1: Record that any compact metric space is automatically second-countable,
  -- because compactness implies properness and proper metric spaces carry a second-countable topology.
  have hSecond : SecondCountableTopology K := inferInstance
  -- Step 2: Use the abstract second-countability machinery to select an explicit countable basis.
  obtain ⟨B, hBcount, -, hBbasis⟩ :=
    TopologicalSpace.exists_countable_basis (α := K)
  -- Step 3: Package the countable family `B` and its basis property to conclude the statement.
  exact ⟨B, hBcount, hBbasis⟩
