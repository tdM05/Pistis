import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that the intersection of an arbitrary nonempty collection of normal subgroups of a group is a normal subgroup (do not assume the collection is countable).
-/

/-Informal Proof

Let $\left\{H_i \mid i \in I\right\}$ be an arbitrary collection of normal subgroups of $G$ and consider the intersection
$$
\bigcap_{i \in I} H_i
$$
Take an element $a$ in the intersection and an arbitrary element $g \in G$. Then $g a g^{-1} \in H_i$ because $H_i$ is normal for any $i \in H$
By the definition of the intersection, this shows that $g a g^{-1} \in \bigcap_{i \in I} H_i$ and therefore it is a normal subgroup.
-/

theorem Dummit_Foote_exercise_3_1_22b {G : Type*} [Group G] (I : Type*) [Nonempty I]
  (H : I → Subgroup G) (hH : ∀ i : I, Normal (H i)) :
  Normal (⨅ (i : I), H i):= by
  -- Step 1: Recognize that the infimum `⨅ (i : I), H i` is definitionally the `iInf` of the family `H`.
  -- Step 2: Aim to invoke `Subgroup.normal_iInf_normal`, which states that the infimum of normal subgroups is normal.
  -- Step 2.1: Supply the lemma with the hypothesis `hH`, witnessing that each `H i` is normal.
  exact Subgroup.normal_iInf_normal (fun i => hH i)
