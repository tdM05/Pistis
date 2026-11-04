import Mathlib
import Pistis
import items.item223.cyclic_lemmas

open Subgroup Set

/-- Segment 223.1: "Suppose H is a maximal subgroup of G." Under the backward arm this is the
supposition `B` itself. -/
theorem helper_Dummit_Foote_exercise_2_4_16c_step1 {G : Type*} [Group G] (H : Subgroup G)
    (hB : H ≠ ⊤ ∧ ∀ K : Subgroup G, H ≤ K → K = H ∨ K = ⊤) :
    H ≠ ⊤ ∧ ∀ K : Subgroup G, H ≤ K → K = H ∨ K = ⊤ := hB
