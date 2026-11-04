import Mathlib
import Pistis

open Filter Set TopologicalSpace
open scoped Topology

theorem helper_Munkres_exercise_13_4a1_step5 {X I : Type*} (T : I → Set (Set X))
    (h : ∀ i : I,
      (univ : Set X) ∈ T i ∧
      (∀ s t, s ∈ T i → t ∈ T i → s ∩ t ∈ T i) ∧
      (∀ s, (∀ t ∈ s, t ∈ T i) → Set.sUnion s ∈ T i)) :
    ∀ (n : ℕ) (U : Fin n → Set X), (∀ k : Fin n, U k ∈ (⋂ i : I, T i)) →
      ∀ i : I, (⋃ k, U k) ∈ T i := by
  intro n U hU i
  have hunion := (h i).2.2
  have hrange : (⋃ k, U k) = ⋃₀ (Set.range U) := by
    rw [sUnion_range]
  rw [hrange]
  apply hunion
  intro t ht
  rw [Set.mem_range] at ht
  obtain ⟨k, rfl⟩ := ht
  have := hU k
  rw [mem_iInter] at this
  exact this i
