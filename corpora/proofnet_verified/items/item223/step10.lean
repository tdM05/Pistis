import Mathlib
import Pistis

/-- Segment 223.10: `p ∣ d ∣ n` so `p ∣ n`, hence `(p,n) = p > 1`, contradicting `(p,n) = 1`. -/
theorem helper_Dummit_Foote_exercise_2_4_16c_step10 (n k p : ℕ) (hp_prime : Prime p)
    (step9 : Nat.gcd p n = 1)
    (asm10_0 : p ∣ Nat.gcd n k ∧ Nat.gcd n k ∣ n) :
    False := by
  obtain ⟨hpd, hdn⟩ := asm10_0
  have hpn : p ∣ n := hpd.trans hdn
  have : p ∣ Nat.gcd p n := Nat.dvd_gcd (dvd_refl p) hpn
  rw [step9] at this
  exact hp_prime.ne_one (Nat.eq_one_of_dvd_one this)
