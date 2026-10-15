import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Let $p \colon X \rightarrow Y$ be an open map. Show that if $A$ is open in $X$, then the map $q \colon A \rightarrow p(A)$ obtained by restricting $p$ is an open map.
-/

/-Informal Proof

Let $U$ be open in $A$. Since $A$ is open in $X, U$ is open in $X$ as well, so $p(U)$ is open in $Y$. Since $q(U)=p(U)=p(U) \cap p(A)$, the set $q(U)$ is open in $p(A)$. Thus $q$ is an open map.
-/

theorem Munkres_exercise_22_5 {X Y : Type*} [TopologicalSpace X]
  [TopologicalSpace Y] (p : X → Y) (hp : IsOpenMap p)
  (A : Set X) (hA : IsOpen A) : IsOpenMap (p ∘ Subtype.val : A → Y) := by
  -- Step 1: Register that the inclusion `Subtype.val : A → X` is itself an open map
  --         because `A` is assumed to be an open subset of `X`.
  have h_inclusion : IsOpenMap (Subtype.val : A → X) := by
    -- Step 1.1: Directly apply the library lemma turning an open subset into an open map.
    exact hA.isOpenMap_subtype_val
  -- Step 2: Combine the open inclusion with the original open map `p`
  --         to deduce that their composition remains an open map.
  -- Step 2.1: Invoke the compositionality lemma for open maps and rewrite the goal.
  simpa [Function.comp] using hp.comp h_inclusion

/-
The original formalization proves `IsOpenMap (p ∘ Subtype.val : A → Y)`, i.e., images of
open sets in A are open in Y. The informal statement asks for something slightly weaker:
that the restricted map `q : A → p(A)` is an open map, meaning images are open in p(A)
with the subspace topology. "Open in Y" implies "open in p(A)" but not conversely in
general, so the original formalization is strictly stronger than the informal statement.

Under the given hypotheses (p is open, A is open in X) both are true — and the informal
proof itself establishes the stronger fact as an intermediate step — but the formal
conclusion should match what was literally asked.

The corrected version below restricts the codomain to `p '' A` (with its subspace topology)
and shows the resulting map `A → p '' A` is an open map.
-/
theorem Munkres_exercise_22_5_corrected {X Y : Type*} [TopologicalSpace X]
  [TopologicalSpace Y] (p : X → Y) (hp : IsOpenMap p)
  (A : Set X) (hA : IsOpen A) :
  IsOpenMap (Set.MapsTo.restrict p A (p '' A) (Set.mapsTo_image p A)) := by
  -- Step 1: Apply the library lemma `IsOpenMap.mapsToRestrict` which states that
  --   an open map restricted to an open source set, with codomain restricted to any
  --   superset of the image, remains an open map on the subspace.
  exact hp.mapsToRestrict hA (Set.mapsTo_image p A)
