import Mathlib
import Pistis

open Set

theorem helper_Dummit_Foote_exercise_7_3_16_step3 {S : Type*} [Ring S] (x : S) :
    x ∈ (Set.univ : Set S) := Set.mem_univ x
