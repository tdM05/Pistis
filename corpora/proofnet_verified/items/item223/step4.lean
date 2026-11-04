import Mathlib
import Pistis
import items.item223.cyclic_lemmas

open Subgroup Set Item223

/-- Segment 223.4: since `H = ⟨x^k⟩` is proper, `d = (n,k) > 1`. -/
theorem helper_Dummit_Foote_exercise_2_4_16c_step4 {n : ℕ+} {G : Type*} [Group G] {x : G}
    (hx : orderOf x = n) (hG : Subgroup.closure ({x} : Set G) = ⊤) (H : Subgroup G) (k : ℕ)
    (hk2 : H = Subgroup.closure {x ^ k}) (asm4_0 : H ≠ ⊤) :
    1 < Nat.gcd (n : ℕ) k := by
  have hne0 : Nat.gcd (n : ℕ) k ≠ 0 := by
    intro h0
    have : (n : ℕ) = 0 := Nat.eq_zero_of_gcd_eq_zero_left h0
    exact absurd this (by exact_mod_cast n.pos.ne')
  have hne1 : Nat.gcd (n : ℕ) k ≠ 1 := by
    intro h1
    have htop : Subgroup.closure {x ^ k} = ⊤ := by
      rw [closure_pow_eq_top_iff_gcd k hG, hx]; exact h1
    rw [← hk2] at htop; exact asm4_0 htop
  omega
