import Mathlib
import Pistis

open Filter Set TopologicalSpace
open scoped Topology

theorem helper_Munkres_exercise_13_4a1_step4 {X I : Type*} (T : I → Set (Set X))
    (h : ∀ i : I,
      (univ : Set X) ∈ T i ∧
      (∀ s t, s ∈ T i → t ∈ T i → s ∩ t ∈ T i) ∧
      (∀ s, (∀ t ∈ s, t ∈ T i) → Set.sUnion s ∈ T i)) :
    ∀ (s : Set (Set X)), (∀ V ∈ s, V ∈ (⋂ j : I, T j)) → ⋃₀ s ∈ (⋂ i : I, T i) := by
  intro s hs
  rw [mem_iInter]
  intro i
  have hunion := (h i).2.2
  apply hunion
  intro t ht
  have := hs t ht
  rw [mem_iInter] at this
  exact this i
