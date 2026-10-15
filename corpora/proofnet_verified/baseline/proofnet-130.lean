import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Show that a closed subspace of a normal space is normal.
-/

/-Informal Proof

Let $X$ be a normal space and $Y$ a closed subspace of $X$.
First we shows that $Y$ is a $T_1$-space.
Let $y \in Y$ be any point. Since $X$ is normal, $X$ is also a $T_1$ space and therefore $\{y\}$ is closed in $X$.
Then it follows that $\{y\}=\{y\} \cap Y$ is closed in $Y$ (in relative topology).
Now let's prove that $X$ is a $T_4$-space.
Let $F, G \subseteq Y$ be disjoint closed sets. Since $F$ and $G$ are closed in $Y$ and $Y$ is closed in $X$, it follows that $F$ and $G$ are closed in $X$.

Since $X$ is normal, $X$ is also a $T_4$-space and therefore there exist disjoint open sets $U, V \subseteq$ $X$ such that $F \subseteq U$ and $G \subseteq V$.
However, then $U \cap Y$ and $V \cap Y$ are open disjoint sets in $Y$ (in relative topology) which separate $F$ and $G$.
-/

theorem Munkres_exercise_32_1 {X : Type*} [TopologicalSpace X]
  (hX : NormalSpace X) (A : Set X) (hA : IsClosed A) :
  NormalSpace {x // x ∈ A} := by
  classical
  -- Step 1: turn the hypothesis `hX` into a typeclass instance so that Lean can
  -- use the normality of `X` implicitly in downstream lemmas.
  haveI : NormalSpace X := hX
  -- Step 2: realize the inclusion `Subtype.val : {x // x ∈ A} → X` as a closed
  -- embedding; this uses that `A` is a closed subset of `X`.
  have hClosedEmbedding :
      Topology.IsClosedEmbedding (Subtype.val : {x // x ∈ A} → X) := by
    -- Step 2.1: apply the mathlib lemma that a closed set induces a closed
    -- embedding of the corresponding subtype into the ambient space.
    simpa using hA.isClosedEmbedding_subtypeVal
  -- Step 3: closed embeddings into a normal space inherit normality, so the
  -- subtype `{x // x ∈ A}` is normal by `Topology.IsClosedEmbedding.normalSpace`.
  exact hClosedEmbedding.normalSpace
