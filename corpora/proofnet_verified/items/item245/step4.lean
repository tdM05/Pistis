import Mathlib
import Pistis

open Set

theorem helper_Dummit_Foote_exercise_7_3_16_step4 {R S : Type*} [Ring R] [Ring S]
    {φ : R →+* S} (x : S) (asm4_0 : Function.Surjective φ) :
    ∃ y : R, φ y = x := asm4_0 x
