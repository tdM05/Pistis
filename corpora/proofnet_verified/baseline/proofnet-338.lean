import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

If $A$ and $B$ are disjoint closed sets in some metric space $X$, prove that they are separated.
-/

/-Informal Proof

We are given that $A \cap B=\varnothing$. Since $A$ and $B$ are closed, this means $A \cap \bar{B}=\varnothing=\bar{A} \cap B$, which says that $A$ and $B$ are separated.
-/

theorem Rudin_exercise_2_19a {X : Type*} [MetricSpace X]
  (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
  SeparatedNhds A B := by
  -- Step 0: Enable classical logic so that set-theoretic reasoning can freely use choice.
  classical
  -- Step 1: Use that every metric space is automatically a normal space (NormalSpace instance).
  -- Step 1.1: Instantiate the `NormalSpace` structure coming from the metric space assumption.
  haveI : NormalSpace X := inferInstance
  -- Step 2: Apply the normal separation theorem to the closed, disjoint sets `A` and `B`.
  -- Step 2.1: Feed in the closedness of `A` provided by `hA`.
  -- Step 2.2: Feed in the closedness of `B` provided by `hB`.
  -- Step 2.3: Feed in the disjointness assumption `hAB` to obtain the required separation.
  exact normal_separation hA hB hAB

/-
The original formalization is not faithful to the informal statement.

The informal statement asks to prove that disjoint closed sets A and B are "separated" in
Rudin's sense (Definition 2.45): A ∩ closure(B) = ∅ and closure(A) ∩ B = ∅. The Lean
formalization instead concludes `SeparatedNhds A B`, which asserts the existence of disjoint
open neighborhoods U ⊇ A, V ⊇ B. This is strictly stronger than Rudin's "separated":
`SeparatedNhds` implies Rudin's separation, but not conversely in general.

While both properties hold for disjoint closed sets in metric spaces (which are normal),
the Lean theorem proves more than what the informal statement asks. The correction uses the
literal definition of Rudin's "separated": A ∩ closure(B) = ∅ ∧ closure(A) ∩ B = ∅.
-/

theorem Rudin_exercise_2_19a_corrected {X : Type*} [MetricSpace X]
  (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
  A ∩ closure B = ∅ ∧ closure A ∩ B = ∅ := by
  -- Step 1: extract A ∩ B = ∅ from the disjointness hypothesis.
  have hAB_empty : A ∩ B = ∅ := Set.disjoint_iff_inter_eq_empty.mp hAB
  constructor
  · -- Step 2: since B is closed, closure B = B, so A ∩ closure B = A ∩ B = ∅.
    rw [hB.closure_eq]; exact hAB_empty
  · -- Step 3: since A is closed, closure A = A, so closure A ∩ B = A ∩ B = ∅.
    rw [hA.closure_eq]; exact Set.inter_comm A B ▸ hAB_empty
