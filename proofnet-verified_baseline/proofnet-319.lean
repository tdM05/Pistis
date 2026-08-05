import Mathlib

open Filter Real Function
open scoped Topology



/-Informal Statement

Prove that a set $U \subset M$ is open if and only if none of its points are limits of its complement.
-/

/-Informal Proof

Assume that none of the points of $U$ are limits of its complement, and let us prove that $U$ is open. Assume by contradiction that $U$ is not open, so there exists $p \in M$ so that $\forall r>0$ there exists $q \in M$ with $d(p, q)<r$ but $q \notin U$. Applying this to $r=1 / n$ we obtain $q_n \in U^c$ such that $d\left(q_n, p\right)<1 / n$. But then $q_n \rightarrow p$ and $p$ is a limit of a sequence of points in $U^c$, a contradiction.

Assume now that $U$ is open. Assume by contradiction there exists $p \in U$ and $p_n \in U^c$ such that $p_n \rightarrow p$. Since $U$ is open, there exists $r>0$ such that $d(p, x)<r$ for $x \in M$ implies $x \in U$. But since $p_n \rightarrow p$, there exists $n_0 \in \mathbb{N}$ such that $n \geq n_0$ implies $d\left(p_n, p\right)<r$, therefore $p_n \in U$ for $n \geq n_0$, a contradiction since $p_n \in U^c$.
-/

theorem Pugh_exercise_2_26 {M : Type*} [TopologicalSpace M]
  (U : Set M) : IsOpen U ↔ ∀ x ∈ U, ¬ ClusterPt x (𝓟 Uᶜ) := by
  -- Step 0: Enable classical logic so that we can use choice-based lemmas about closures.
  classical
  constructor
  · -- Step 1: Prove that an open set contains no cluster point of its complement.
    intro hU x hx hCluster
    -- Step 1.1: Translate the cluster-point hypothesis into the statement that `x` lies in the closure of `Uᶜ`.
    have hxClosure : x ∈ closure Uᶜ := by
      -- Step 1.1.1: `mem_closure_iff_clusterPt` converts the cluster-point statement into closure membership.
      simpa using (mem_closure_iff_clusterPt (x := x) (s := Uᶜ)).2 hCluster
    -- Step 1.2: Since the complement of an open set is closed, its closure equals itself.
    have hClosed : IsClosed Uᶜ := hU.isClosed_compl
    have hxCompl : x ∈ Uᶜ := by
      -- Step 1.2.1: Rewrite `hxClosure` via `closure_eq` for the closed set `Uᶜ`.
      simpa [hClosed.closure_eq] using hxClosure
    -- Step 1.3: Derive the contradiction `False` because `x` cannot simultaneously belong to `U` and `Uᶜ`.
    exact hxCompl hx
  · -- Step 2: Show that the absence of such cluster points forces `U` to be open.
    intro hClusterFree
    -- Step 2.1: Use the neighborhood characterization of openness.
    refine isOpen_iff_mem_nhds.mpr ?_
    intro x hx
    -- Step 2.1.1: Convert the assumption “`x` is not a cluster point of `Uᶜ`” into “`x` lies in the interior of `U`”.
    have hxInterior : x ∈ interior U := by
      -- Step 2.1.1.1: Apply the equivalence between interior points and non-cluster points of the complement.
      exact (mem_interior_iff_not_clusterPt_compl).2 (hClusterFree x hx)
    -- Step 2.1.2: Translate the interior membership into the fact that `U` itself is a neighborhood of `x`.
    exact (mem_interior_iff_mem_nhds).1 hxInterior
