import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Show that every locally compact Hausdorff space is completely regular.
-/

/-Informal Proof

$X$ is a subspace of a compact Hausdorff space $Y$, its one-point compactification. $Y$ is normal, and so by the Urysohn lemma $Y$ is completely regular. Therefore by corollary $X$ is completely regular.
-/

theorem Munkres_exercise_33_7 {X : Type*} [TopologicalSpace X]
  (hX : LocallyCompactSpace X) (hX' : T2Space X) :
  CompletelyRegularSpace X := by
  classical
  -- Step 1: Register that the one-point compactification inherits complete regularity.
  -- Step 1.1: A locally compact Hausdorff space yields a normal, hence completely regular,
  --           one-point compactification via existing Mathlib instances.
  have hOnePoint : CompletelyRegularSpace (OnePoint X) := by
    infer_instance
  -- Step 2: Record that the canonical inclusion `X → OnePoint X` is inducing.
  -- Step 2.1: This follows from the fact that the inclusion is an open embedding.
  have hInducing : Topology.IsInducing ((↑) : X → OnePoint X) := by
    simpa using OnePoint.isOpenEmbedding_coe.isInducing
  -- Step 3: Transport complete regularity along the inducing map.
  -- Step 3.1: Applying the general lemma for inducing maps finishes the job.
  haveI := hOnePoint
  exact hInducing.completelyRegularSpace
