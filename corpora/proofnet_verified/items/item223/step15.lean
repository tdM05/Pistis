import Mathlib
import Pistis

/-- Segment 223.15: the only divisors of the prime `pc` are `1` and `pc`. -/
theorem helper_Dummit_Foote_exercise_2_4_16c_step15 (pc : ℕ) (hpc_prime : Prime pc) :
    ∀ m : ℕ, m ∣ pc → m = 1 ∨ m = pc := by
  intro m hm
  exact (Nat.Prime.eq_one_or_self_of_dvd hpc_prime.nat_prime m hm)
