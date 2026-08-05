import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Let $G$ be a topological group; let $C$ be the component of $G$ containing the identity element $e$. Show that $C$ is a normal subgroup of $G$.
-/

/-Informal Proof

Given $x \in G$, the maps $y \mapsto x y$ and $y \mapsto y x$ are homeomorphisms of $G$ onto itself. Since $C$ is a component, $x C$ and $C x$ are both components that contain $x$, so they are equal. Hence $x C=C x$ for all $x \in G$, so $C$ is a normal subgroup of $G$.
-/

theorem Munkres_exercise_25_9 {G : Type*} [TopologicalSpace G] [Group G]
  [IsTopologicalGroup G] (C : Set G) (hC : C = connectedComponent (1 : G)) :
  ∃ H : Subgroup G, (H : Set G) = C ∧ H.Normal := by
  classical
  -- Step 1: Pick the subgroup consisting of all elements in the connected component of `1`.
  refine ⟨Subgroup.connectedComponentOfOne G, ?_, ?_⟩
  -- Step 2: Identify its underlying set with the given component `C`.
  -- Step 2.1: By definition the carrier is `connectedComponent 1`, so we just rewrite using `hC`.
  · simp [Subgroup.connectedComponentOfOne, hC]
  -- Step 3: Prove this subgroup is normal by showing it is closed under conjugation.
  -- Step 3.1: Expand the definition of `Normal` and fix an arbitrary element of the subgroup.
  · refine ⟨?_⟩
    intro n hn g
    -- Step 3.2: View the assumption `hn` as actual membership in the connected component of `1`.
    -- Step 3.2.1: This is immediate from the definition of `connectedComponentOfOne`.
    have hnC : n ∈ connectedComponent (1 : G) := by
      simpa [Subgroup.connectedComponentOfOne] using hn
    -- Step 3.3: Consider the conjugation map `φ h = g * h * g⁻¹`, which is continuous.
    -- Step 3.3.1: Define this map explicitly for later reference.
    set φ : G → G := fun h => g * h * g⁻¹ with hφ
    -- Step 3.3.2: Record the continuity of `φ` using the topological group structure.
    have hφ_cont : Continuous φ := by
      simpa [φ] using (IsTopologicalGroup.continuous_conj (G := G) g)
    -- Step 3.4: Apply the general lemma that the image of a connected component is included
    --          in the connected component of the image of the distinguished point.
    have hImage :=
      hφ_cont.image_connectedComponent_subset (1 : G)
    -- Step 3.5: The element `φ n` lies in that image, so we can specialize the inclusion.
    have hmem : φ n ∈ φ '' connectedComponent (1 : G) := by
      exact ⟨n, hnC, rfl⟩
    -- Step 3.5.1: Deduce that `φ n` lies in `connectedComponent (φ 1)`, then simplify.
    have htarget : φ n ∈ connectedComponent (φ 1) := hImage hmem
    -- Step 3.6: Rewriting `φ` shows `φ 1 = 1`, so the target component is `connectedComponent 1`.
    --           Hence the conjugate is still in the subgroup, as required.
    simpa [φ, Subgroup.connectedComponentOfOne] using htarget
