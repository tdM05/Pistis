import Mathlib
import Pistis
import items.item223.cyclic_lemmas

open Subgroup Set Item223

/-- Segment 223.12: if `H` is not maximal (in particular `H ≠ ⊤`), then in the finite group there
is a maximal subgroup `K` containing `H`. -/
theorem helper_Dummit_Foote_exercise_2_4_16c_step12 {n : ℕ+} {G : Type*} [Group G] {x : G}
    (hx : orderOf x = n) (hG : Subgroup.closure ({x} : Set G) = ⊤) (H : Subgroup G)
    (hHne : H ≠ ⊤) :
    ∃ K : Subgroup G, (K ≠ ⊤ ∧ ∀ L : Subgroup G, K ≤ L → L = K ∨ L = ⊤) ∧ H ≤ K := by
  haveI : Finite G := finite_of_generator hx n.pos hG
  obtain ⟨K, hHK, hKm⟩ := (Set.toFinite {J : Subgroup G | H ≤ J ∧ J ≠ ⊤}).exists_le_maximal
    (a := H) ⟨le_refl H, hHne⟩
  refine ⟨K, ⟨hKm.prop.2, ?_⟩, hKm.prop.1⟩
  intro L hKL
  by_cases hLtop : L = ⊤
  · right; exact hLtop
  · left
    have hLmem : L ∈ {J : Subgroup G | H ≤ J ∧ J ≠ ⊤} := ⟨le_trans hKm.prop.1 hKL, hLtop⟩
    exact le_antisymm (hKm.le_of_ge hLmem hKL) hKL
