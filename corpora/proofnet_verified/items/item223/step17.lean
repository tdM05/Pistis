import Mathlib
import Pistis

open Subgroup Set

/-- Segment 223.17: both alternatives are impossible for a *proper, maximal* `K` properly
containing `H` unless `H` itself is maximal; this contradiction shows `H` is maximal (`B`). -/
theorem helper_Dummit_Foote_exercise_2_4_16c_step17 {G : Type*} [Group G] (H K : Subgroup G)
    (hKmax : K ≠ ⊤ ∧ ∀ L : Subgroup G, K ≤ L → L = K ∨ L = ⊤) (hHne : H ≠ ⊤)
    (asm17_0 : K = ⊤ ∨ H = K) :
    H ≠ ⊤ ∧ ∀ K : Subgroup G, H ≤ K → K = H ∨ K = ⊤ := by
  rcases asm17_0 with hKtop | hHK
  · exact absurd hKtop hKmax.1
  · refine ⟨hHne, ?_⟩
    intro L hHL
    have hKL : K ≤ L := hHK ▸ hHL
    rcases hKmax.2 L hKL with h | h
    · left; rw [h, hHK]
    · right; exact h
