import Mathlib
import Pistis
import items.item223.cyclic_lemmas

open Subgroup Set Item223

/-- Segment 223.9: `K = ⟨x^p⟩ = G`, so `(p,n) = 1`. -/
theorem helper_Dummit_Foote_exercise_2_4_16c_step9 {n : ℕ+} {G : Type*} [Group G] {x : G}
    (hx : orderOf x = n) (hG : Subgroup.closure ({x} : Set G) = ⊤) (p : ℕ)
    (step8 : Subgroup.closure {x ^ p} = ⊤) :
    Nat.gcd p (n : ℕ) = 1 := by
  have h := (closure_pow_eq_top_iff_gcd p hG).mp step8
  rw [hx, Nat.gcd_comm] at h
  exact h
