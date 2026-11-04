import Mathlib
import Pistis

/-- Segment 223.3: "Let d = (n, k)." -/
theorem helper_Dummit_Foote_exercise_2_4_16c_step3 (n k : ℕ) :
    ∃ d : ℕ, d = Nat.gcd n k := ⟨Nat.gcd n k, rfl⟩
