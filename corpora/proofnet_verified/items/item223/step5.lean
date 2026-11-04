import Mathlib
import Pistis

/-- Segment 223.5: choose a prime factor `p` of `d = (n,k) > 1`. -/
theorem helper_Dummit_Foote_exercise_2_4_16c_step5 (n k : ℕ) (hd1 : 1 < Nat.gcd n k) :
    ∃ p : ℕ, Prime p ∧ p ∣ Nat.gcd n k := by
  obtain ⟨p, hpp, hpd⟩ := (Nat.gcd n k).exists_prime_and_dvd (by omega)
  exact ⟨p, hpp.prime, hpd⟩
