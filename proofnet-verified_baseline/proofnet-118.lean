import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Let $\left\{A_{n}\right\}$ be a sequence of connected subspaces of $X$, such that $A_{n} \cap A_{n+1} \neq \varnothing$ for all $n$. Show that $\bigcup A_{n}$ is connected.
-/

/-Informal Proof

Suppose that $\bigcup_n A_n=B \cup C$, where $B$ and $C$ are disjoint open subsets of $\bigcup_n A_n$. Since $A_1$ is connected and a subset of $B \cup C$, by Lemma $23.2$ it lies entirely within either $B$ or $C$. Without any loss of generality, we may assume $A_1 \subset B$. Note that given $n$, if $A_n \subset B$ then $A_{n+1} \subset B$, for if $A_{n+1} \subset C$ then $A_n \cap A_{n+1} \subset B \cap C=\emptyset$, in contradiction with the assumption. By induction, $A_n \subset B$ for all $n \in \mathbb{Z}_{+}$, so that $\bigcup_n A_n \subset B$. It follows that $\bigcup_n A_n$ is connected.
-/

theorem Munkres_exercise_23_2 {X : Type*}
  [TopologicalSpace X] {A : ℕ → Set X} (hA : ∀ n, IsConnected (A n))
  (hAn : ∀ n, A n ∩ A (n + 1) ≠ ∅) :
  IsConnected (⋃ n, A n) := by
  classical
  -- Step 1: turn each non-emptiness assumption on `A n ∩ A (n + 1)` into a reusable witness.
  have hAdj : ∀ n, (A n ∩ A (n + 1)).Nonempty := by
    -- Step 1.1: rewrite `Nonempty` as `≠ ∅` and apply the given hypothesis.
    intro n
    exact (Set.nonempty_iff_ne_empty).2 (hAn n)
  -- Step 2: encode the “intersection graph” relating indices that share points.
  set R : ℕ → ℕ → Prop := fun i j => (A i ∩ A j).Nonempty
  -- Step 3: register forward and backward edges in this graph using consecutive intersections.
  have hEdgeSucc : ∀ n, R n (n + 1) := by
    -- Step 3.1: unpack the definition of `R` and reuse `hAdj`.
    intro n
    simpa [R, Nat.succ_eq_add_one] using hAdj n
  -- Step 3.2: obtain the reverse edges by symmetry of intersection.
  have hEdgePred : ∀ n, R (n + 1) n := by
    -- Step 3.2.1: rewrite the intersection by commuting the factors.
    intro n
    simpa [R, Nat.succ_eq_add_one, Set.inter_comm] using hAdj n
  -- Step 4: prove that any two indices are connected inside the graph via successive edges.
  have hChain : ∀ i j : ℕ, Relation.ReflTransGen R i j := by
    -- Step 4.1: apply the general lemma for relations on successor-ordered types.
    intro i j
    refine reflTransGen_of_succ R ?_ ?_
    -- Step 4.1.1: furnish forward steps `k → k + 1` along the interval `[i, j)`.
    intro k hk
    exact hEdgeSucc k
    -- Step 4.1.2: furnish backward steps `k + 1 → k` along the interval `[j, i)`.
    intro k hk
    exact hEdgePred k
  -- Step 5: assemble the connectedness of the entire union via the path-connected graph lemma.
  simpa [R] using
    IsConnected.iUnion_of_reflTransGen (s := A) (H := hA) (K := hChain)
