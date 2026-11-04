import Mathlib
import Pistis

open Filter Set TopologicalSpace
open scoped Topology

theorem helper_Munkres_exercise_13_4a1_step2 {X I : Type*} (T : I → Set (Set X)) :
    ∀ (s : Set (Set X)), (∀ V ∈ s, V ∈ (⋂ i : I, T i)) ↔ (∀ V ∈ s, ∀ i : I, V ∈ T i) := by
  intro s
  constructor
  · intro hV V hVs i
    have := hV V hVs
    rw [mem_iInter] at this
    exact this i
  · intro hV V hVs
    rw [mem_iInter]
    intro i
    exact hV V hVs i
