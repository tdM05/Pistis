import Mathlib
import Pistis
import items.item223.cyclic_lemmas

open Subgroup Set Item223

/-- Segment 223.14: `x^p ∈ ⟨x^q⟩`, and since `q` is canonical (`(n,q) = q`) this gives `q ∣ p`. -/
theorem helper_Dummit_Foote_exercise_2_4_16c_step14 {n : ℕ+} {G : Type*} [Group G] {x : G}
    (hx : orderOf x = n) (pc q : ℕ) (hqn : Nat.gcd (n : ℕ) q = q)
    (asm14_0 : x ^ pc ∈ Subgroup.closure {x ^ q}) :
    q ∣ pc := by
  rw [mem_closure_pow_iff_gcd_dvd, hx, hqn] at asm14_0
  exact asm14_0
