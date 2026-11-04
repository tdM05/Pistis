import Mathlib
import Pistis
import items.item223.cyclic_lemmas

open Subgroup Set Item223

/-- Assumption 223.2 ("H is cyclic"): a subgroup of a finite cyclic group is cyclic, hence has a
single generator. -/
theorem helper_Dummit_Foote_exercise_2_4_16c_asm2 {n : ℕ+} {G : Type*} [Group G] {x : G}
    (hx : orderOf x = n) (hG : Subgroup.closure ({x} : Set G) = ⊤) (H : Subgroup G) :
    ∃ g : G, H = Subgroup.closure {g} := by
  haveI : Finite G := finite_of_generator hx n.pos hG
  haveI hcyc : IsCyclic G := by
    rw [isCyclic_iff_exists_zpowers_eq_top]
    exact ⟨x, by rw [← closure_singleton_eq_zpowers, hG]⟩
  haveI hH : IsCyclic H := isCyclic H
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top H).mp hH
  exact ⟨g, by rw [closure_singleton_eq_zpowers, hg]⟩

/-- Segment 223.2: H cyclic and proper, so `H = ⟨x^k⟩` for a *canonical* exponent `k > 1` dividing
`n`. (The natural-language `k` is the divisor exponent its own later steps require: see report.) -/
theorem helper_Dummit_Foote_exercise_2_4_16c_step2 {n : ℕ+} {G : Type*} [Group G] {x : G}
    (hx : orderOf x = n) (hG : Subgroup.closure ({x} : Set G) = ⊤) (H : Subgroup G)
    (hB : H ≠ ⊤ ∧ ∀ K : Subgroup G, H ≤ K → K = H ∨ K = ⊤)
    (asm2_0 : ∃ g : G, H = Subgroup.closure {g}) :
    ∃ k : ℕ, 1 < k ∧ k ∣ (n : ℕ) ∧ H = Subgroup.closure {x ^ k} := by
  haveI : Finite G := finite_of_generator hx n.pos hG
  obtain ⟨g, hgH⟩ := asm2_0
  have hgmem : g ∈ Submonoid.powers x := by
    rw [mem_powers_iff_mem_zpowers, ← closure_singleton_eq_zpowers, hG]; trivial
  obtain ⟨m, hm⟩ := hgmem
  have hHm : H = Subgroup.closure {x ^ m} := by rw [hgH, ← hm]
  refine ⟨Nat.gcd (orderOf x) m, ?_, ?_, ?_⟩
  · have hne0 : Nat.gcd (orderOf x) m ≠ 0 := by
      intro h0
      have : orderOf x = 0 := Nat.eq_zero_of_gcd_eq_zero_left h0
      rw [hx] at this; exact absurd this (by exact_mod_cast n.pos.ne')
    have hne1 : Nat.gcd (orderOf x) m ≠ 1 := by
      intro h1
      have htop : Subgroup.closure {x ^ m} = ⊤ := by rw [closure_pow_eq_top_iff_gcd m hG]; exact h1
      rw [← hHm] at htop; exact hB.1 htop
    omega
  · rw [← hx]; exact Nat.gcd_dvd_left _ _
  · rw [hHm]; exact closure_pow_eq_closure_pow_gcd m
