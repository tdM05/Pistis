import Mathlib
import Pistis

open Set

theorem helper_Dummit_Foote_exercise_7_3_16_step1 {R S : Type*} [Ring R] [Ring S]
    {φ : R →+* S} (r : S) (hr : r ∈ φ '' (center R)) :
    r ∈ φ '' (center R) := hr
