import Mathlib
import Pistis
import items.item245.step1
import items.item245.step2
import items.item245.step3
import items.item245.step4
import items.item245.step5
set_option linter.unusedTactic false

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Let $\varphi: R \rightarrow S$ be a surjective homomorphism of rings. Prove that the image of the center of $R$ is contained in the center of $S$.
-/

theorem Dummit_Foote_exercise_7_3_16 {R S : Type*} [Ring R] [Ring S]
   {φ : R →+* S} (hf : Function.Surjective φ) :
   φ '' (center R) ⊆ center S := by
  pistis_intro "245.0"
    r"Let $\varphi: R \rightarrow S$ be a surjective homomorphism of rings. Prove that the image of the center of $R$ is contained in the center of $S$."

  intro r hr
  pistis_segment "245.1"
    r"Suppose $r \in \varphi[Z(R)]$."
    (step1 : r ∈ φ '' (center R)) := by
      exact helper_Dummit_Foote_exercise_7_3_16_step1 r hr

  pistis_segment "245.2"
    r"Then $r=\varphi(z)$ for some $z \in Z(R)$."
    (step2 : ∃ z ∈ center R, φ z = r) := by
      exact helper_Dummit_Foote_exercise_7_3_16_step2 r step1

  have key : ∀ x : S, x * r = r * x := by
    intro x
    pistis_segment "245.3"
      r"Now let $x \in S$."
      (step3 : x ∈ (Set.univ : Set S)) := by
        exact helper_Dummit_Foote_exercise_7_3_16_step3 x

    pistis_assumption "245.4" r"$\varphi$ is surjective"
      (asm4_0 : Function.Surjective φ) := by exact hf
    pistis_segment "245.4"
      r"Since $\varphi$ is surjective, we have $x=\varphi y$ for some $y \in R$."
      (step4 : ∃ y : R, φ y = x) := by
        exact helper_Dummit_Foote_exercise_7_3_16_step4 x asm4_0

    pistis_segment "245.5"
      r"Now
$$
x r=\varphi(y) \varphi(z)=\varphi(y z)=\varphi(z y)=\varphi(z) \varphi(y)=r x .
$$"
      (step5 : x * r = r * x) := by
        exact helper_Dummit_Foote_exercise_7_3_16_step5 x r step2 step4
    exact step5

  pistis_conclude "245.6"
    r"Thus $r \in Z(S)$."

  have hmem : r ∈ center S := by
    rw [Set.mem_center_iff]
    refine ⟨fun a => (key a).symm, fun b c => (mul_assoc r b c).symm, fun a b => mul_assoc a b r⟩
  exact hmem
