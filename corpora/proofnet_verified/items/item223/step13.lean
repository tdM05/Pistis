import Mathlib
import Pistis
import items.item223.cyclic_lemmas

open Subgroup Set Item223

/-- Segment 223.13: the subgroup `K` is cyclic, `K = ⟨x^q⟩` for a canonical exponent `q` (with
`(n,q) = q`, i.e. `q ∣ n`). -/
theorem helper_Dummit_Foote_exercise_2_4_16c_step13 {n : ℕ+} {G : Type*} [Group G] {x : G}
    (hx : orderOf x = n) (hG : Subgroup.closure ({x} : Set G) = ⊤) (K : Subgroup G) :
    ∃ q : ℕ, K = Subgroup.closure {x ^ q} ∧ Nat.gcd (n : ℕ) q = q := by
  haveI : Finite G := finite_of_generator hx n.pos hG
  haveI hcyc : IsCyclic G := by
    rw [isCyclic_iff_exists_zpowers_eq_top]
    exact ⟨x, by rw [← closure_singleton_eq_zpowers, hG]⟩
  haveI hKc : IsCyclic K := isCyclic K
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top K).mp hKc
  have hgmem : g ∈ Submonoid.powers x := by
    rw [mem_powers_iff_mem_zpowers, ← closure_singleton_eq_zpowers, hG]; trivial
  obtain ⟨q0, hq0⟩ := hgmem
  have hgq : x ^ q0 = g := hq0
  have hKc0 : K = Subgroup.closure {x ^ q0} := by
    rw [closure_singleton_eq_zpowers, hgq, hg]
  refine ⟨Nat.gcd (n : ℕ) q0, ?_, ?_⟩
  · rw [hKc0, closure_pow_eq_iff_gcd, hx]
    exact (Nat.gcd_eq_right (Nat.gcd_dvd_left _ _)).symm
  · exact Nat.gcd_eq_right (Nat.gcd_dvd_left _ _)
