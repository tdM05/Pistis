import Mathlib
import Pistis

open Set

theorem helper_Dummit_Foote_exercise_7_3_16_step5 {R S : Type*} [Ring R] [Ring S]
    {φ : R →+* S} (x r : S)
    (step2 : ∃ z ∈ center R, φ z = r) (step4 : ∃ y : R, φ y = x) :
    x * r = r * x := by
  obtain ⟨z, hz, hzr⟩ := step2
  obtain ⟨y, hyx⟩ := step4
  subst hyx hzr
  rw [← map_mul, ← map_mul]
  congr 1
  rw [Set.mem_center_iff] at hz
  exact (hz.comm y).symm
