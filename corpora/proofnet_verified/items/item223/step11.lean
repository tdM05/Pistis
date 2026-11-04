import Mathlib
import Pistis

open Subgroup Set

/-- Segment 223.11 (seam): the first implication is done; for the converse we *suppose*
`H = ⟨x^p⟩` for a prime `p` dividing `n` — i.e. the forward arm's hypothesis `A`. -/
theorem helper_Dummit_Foote_exercise_2_4_16c_step11 {n : ℕ+} {G : Type*} [Group G] {x : G}
    (H : Subgroup G)
    (hA : ∃ p : ℕ, Prime p ∧ p ∣ (n : ℕ) ∧ H = Subgroup.closure {x ^ p}) :
    ∃ p : ℕ, Prime p ∧ p ∣ (n : ℕ) ∧ H = Subgroup.closure {x ^ p} := hA
