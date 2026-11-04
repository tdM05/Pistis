import Mathlib
import Pistis

open Subgroup Set

/-- Segment 223.16: `q ∣ pc` and `pc` prime force `q = 1` or `q = pc`; the first makes `K = G`,
the second makes `H = K`. -/
theorem helper_Dummit_Foote_exercise_2_4_16c_step16 {G : Type*} [Group G] (H K : Subgroup G)
    (q pc : ℕ) (step14 : q ∣ pc) (step15 : ∀ m : ℕ, m ∣ pc → m = 1 ∨ m = pc)
    (asm16_0 : q = 1 → K = ⊤) (asm16_1 : q = pc → H = K) :
    K = ⊤ ∨ H = K := by
  rcases step15 q step14 with h | h
  · left; exact asm16_0 h
  · right; exact asm16_1 h
