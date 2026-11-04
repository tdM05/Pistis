import Mathlib
import Pistis

open Subgroup Set

/-- Segment 223.8: `H` maximal and `H < K = ⟨x^p⟩`, so `K = G`. -/
theorem helper_Dummit_Foote_exercise_2_4_16c_step8 {G : Type*} [Group G] {x : G} (H : Subgroup G)
    (p : ℕ) (hlt : H < Subgroup.closure {x ^ p})
    (asm8_0 : H ≠ ⊤ ∧ ∀ K : Subgroup G, H ≤ K → K = H ∨ K = ⊤) :
    Subgroup.closure {x ^ p} = ⊤ := by
  rcases asm8_0.2 _ (le_of_lt hlt) with h | h
  · exact absurd h.symm (ne_of_lt hlt)
  · exact h
