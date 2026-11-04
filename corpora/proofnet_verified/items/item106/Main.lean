import Mathlib
import Pistis
import items.item106.step1
import items.item106.step2
import items.item106.step3
import items.item106.step4
import items.item106.step5
import items.item106.step6
set_option linter.unusedTactic false

open Filter Set TopologicalSpace
open scoped Topology

def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

/-Informal Statement

If $\mathcal{T}_\alpha$ is a family of topologies on $X$, show that $\bigcap \mathcal{T}_\alpha$ is a topology on $X$.
-/

theorem Munkres_exercise_13_4a1 (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  is_topology X (⋂ i : I, T i) := by
  pistis_intro "106.0"
    r"If $\mathcal{T}_\alpha$ is a family of topologies on $X$, show that $\bigcap \mathcal{T}_\alpha$ is a topology on $X$."

  pistis_assumption "106.1" r"$\emptyset$ and $X$ belong to $\mathcal{T}_\alpha$ for each $\alpha$"
    (asm1_0 : ∀ i : I, (∅ : Set X) ∈ T i ∧ (univ : Set X) ∈ T i) := by
      intro i
      refine ⟨?_, (h i).1⟩
      have hemp : (⋃₀ (∅ : Set (Set X))) ∈ T i := (h i).2.2 ∅ (by simp)
      simpa using hemp
  pistis_segment "106.1"
    r"Since $\emptyset$ and $X$ belong to $\mathcal{T}_\alpha$ for each $\alpha$, they belong to $\bigcap_\alpha \mathcal{T}_\alpha$."
    (step1 : (∅ : Set X) ∈ (⋂ i : I, T i) ∧ (univ : Set X) ∈ (⋂ i : I, T i)) := by
      exact helper_Munkres_exercise_13_4a1_step1 T asm1_0

  pistis_segment "106.2"
    r"Let $\left\{V_\beta\right\}_\beta$ be a collection of open sets in $\bigcap_\alpha \mathcal{T}_\alpha$."
    (step2 : ∀ (s : Set (Set X)), (∀ V ∈ s, V ∈ (⋂ i : I, T i)) ↔ (∀ V ∈ s, ∀ i : I, V ∈ T i)) := by
      exact helper_Munkres_exercise_13_4a1_step2 T

  pistis_assumption "106.3" r"$\mathcal{T}_\alpha$ is a topology on $X$"
    (asm3_0 : ∀ i : I, is_topology X (T i)) := by assumption
  pistis_segment "106.3"
    r"For any fixed $\alpha$ we have $\cup_\beta V_\beta \in \mathcal{T}_\alpha$ since $\mathcal{T}_\alpha$ is a topology on $X$,"
    (step3 : ∀ (i : I) (s : Set (Set X)), (∀ V ∈ s, V ∈ (⋂ j : I, T j)) → ⋃₀ s ∈ T i) := by
      exact helper_Munkres_exercise_13_4a1_step3 T asm3_0

  pistis_segment "106.4"
    r"so $\bigcup_\beta V_\beta \in \bigcap_\alpha \mathcal{T}_\alpha$."
    (step4 : ∀ (s : Set (Set X)), (∀ V ∈ s, V ∈ (⋂ j : I, T j)) → ⋃₀ s ∈ (⋂ i : I, T i)) := by
      exact helper_Munkres_exercise_13_4a1_step4 T h

  pistis_segment "106.5"
    r"Similarly, if $U_1, \ldots, U_n$ are elements of $\bigcap_\alpha \mathcal{T}_\alpha$, then for each $\alpha$ we have $\bigcup_{i=1}^n U_i \in \mathcal{T}_\alpha$"
    (step5 : ∀ (n : ℕ) (U : Fin n → Set X), (∀ k : Fin n, U k ∈ (⋂ i : I, T i)) → ∀ i : I, (⋃ k, U k) ∈ T i) := by
      exact helper_Munkres_exercise_13_4a1_step5 T h

  pistis_segment "106.6"
    r"and therefore $\bigcup_{i=1}^n U_i \in \bigcap_\alpha \mathcal{T}_\alpha$."
    (step6 : ∀ (n : ℕ) (U : Fin n → Set X), (∀ k : Fin n, U k ∈ (⋂ i : I, T i)) → (⋃ k, U k) ∈ (⋂ i : I, T i)) := by
      exact helper_Munkres_exercise_13_4a1_step6 T h

  pistis_conclude "106.7"
    r"It follows that $\bigcap_\alpha \mathcal{T}_\alpha$ is a topology on $X$."

  have hbinary : ∀ s t, s ∈ (⋂ i : I, T i) → t ∈ (⋂ i : I, T i) → s ∩ t ∈ (⋂ i : I, T i) := by
    intro s t hs ht
    rw [mem_iInter]
    intro i
    rw [mem_iInter] at hs ht
    exact (h i).2.1 s t (hs i) (ht i)
  exact ⟨step1.2, hbinary, step4⟩
