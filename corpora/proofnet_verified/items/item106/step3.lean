import Mathlib
import Pistis

open Filter Set TopologicalSpace
open scoped Topology

theorem helper_Munkres_exercise_13_4a1_step3 {X I : Type*} (T : I → Set (Set X))
    (asm3_0 : ∀ i : I,
      (univ : Set X) ∈ T i ∧
      (∀ s t, s ∈ T i → t ∈ T i → s ∩ t ∈ T i) ∧
      (∀ s, (∀ t ∈ s, t ∈ T i) → Set.sUnion s ∈ T i)) :
    ∀ (i : I) (s : Set (Set X)), (∀ V ∈ s, V ∈ (⋂ j : I, T j)) → ⋃₀ s ∈ T i := by
  intro i s hs
  have hunion := (asm3_0 i).2.2
  apply hunion
  intro t ht
  have := hs t ht
  rw [mem_iInter] at this
  exact this i
