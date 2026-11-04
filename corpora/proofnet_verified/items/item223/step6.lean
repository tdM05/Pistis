import Mathlib
import Pistis

/-- Segment 223.6 (case `k = p = d`): then `k ∣ n`, since `k = d = (n,k)` and `(n,k) ∣ n`. -/
theorem helper_Dummit_Foote_exercise_2_4_16c_step6 (n k p : ℕ)
    (asm6_0 : k = p ∧ p = Nat.gcd n k) :
    k ∣ n := by
  obtain ⟨hkp, hpd⟩ := asm6_0
  -- k = p = (n,k), and (n,k) ∣ n
  have hkd : k = Nat.gcd n k := hkp.trans hpd
  rw [hkd]
  exact Nat.gcd_dvd_left _ _
