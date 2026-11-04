import Mathlib
import Pistis

open Filter Set TopologicalSpace
open scoped Topology

theorem helper_Munkres_exercise_13_4a1_step1 {X I : Type*} (T : I → Set (Set X))
    (asm1_0 : ∀ i : I, (∅ : Set X) ∈ T i ∧ (univ : Set X) ∈ T i) :
    (∅ : Set X) ∈ (⋂ i : I, T i) ∧ (univ : Set X) ∈ (⋂ i : I, T i) := by
  constructor
  · rw [mem_iInter]
    intro i
    exact (asm1_0 i).1
  · rw [mem_iInter]
    intro i
    exact (asm1_0 i).2
