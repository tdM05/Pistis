import Mathlib
import Pistis

open Set

theorem helper_Dummit_Foote_exercise_7_3_16_step2 {R S : Type*} [Ring R] [Ring S]
    {φ : R →+* S} (r : S) (step1 : r ∈ φ '' (center R)) :
    ∃ z ∈ center R, φ z = r := by
  obtain ⟨z, hz, hzr⟩ := step1
  exact ⟨z, hz, hzr⟩
