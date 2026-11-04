import Mathlib
import Pistis
import items.item223.cyclic_lemmas

open Subgroup Set Item223

/-- Segment 223.7 (reductio: `p` a proper divisor of `k`): `H = ⟨x^k⟩ < ⟨x^p⟩ = K`. -/
theorem helper_Dummit_Foote_exercise_2_4_16c_step7 {n : ℕ+} {G : Type*} [Group G] {x : G}
    (hx : orderOf x = n) (H : Subgroup G) (k p : ℕ)
    (hk2 : H = Subgroup.closure {x ^ k}) (hkn : k ∣ (n : ℕ)) (hpn : p ∣ (n : ℕ))
    (asm7_0 : p ∣ k ∧ p ≠ k) :
    H < Subgroup.closure {x ^ p} := by
  obtain ⟨hpk, hpne⟩ := asm7_0
  have hgcd_nk : Nat.gcd (n : ℕ) k = k := Nat.gcd_eq_right hkn
  rw [hk2, lt_iff_le_and_ne]
  refine ⟨?_, ?_⟩
  · rw [closure_pow_le_iff_gcd_dvd, hx, hgcd_nk]
    exact (Nat.gcd_dvd_right (n : ℕ) p).trans hpk
  · rw [Ne, closure_pow_eq_iff_gcd, hx, hgcd_nk, Nat.gcd_eq_right hpn]
    exact fun h => hpne h.symm
