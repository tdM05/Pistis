import Mathlib

open Filter Real Function
open scoped Topology



/-Informal Statement

Assume that $A, B$ are compact, disjoint, nonempty subsets of $M$. Prove that there are $a_0 \in A$ and $b_0 \in B$ such that for all $a \in A$ and $b \in B$ we have $d(a_0, b_0) \leq d(a, b)$.
-/

/-Informal Proof

Let $A$ and $B$ be compact, disjoint and non-empty subsets of $M$. We want to show that there exist $a_0 \in A, b_0 \in B$ such that for all $a \in A, b \in B$,
$$
d\left(a_0, b_0\right) \leq d(a, b) .
$$
We saw in class that the distance function $d: M \times M \rightarrow \mathbb{R}$ is continuous. We also saw in class that any continuous, real-valued function assumes maximum and minimum values on a compact set. Since $A$ and $B$ are compact, $A \times B$ is (non-empty) compact in $M \times M$. Therefore there exists $\left(a_0, b_0\right) \in A \times B$ such that $d\left(a_0, b_0\right) \leq d(a, b), \forall(a, b) \in A \times B$.
-/

theorem Pugh_exercise_2_46 {M : Type*} [MetricSpace M]
  {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
  (hAB : Disjoint A B) (hA₀ : A ≠ ∅) (hB₀ : B ≠ ∅) :
  ∃ a₀ b₀, a₀ ∈ A ∧ b₀ ∈ B ∧ ∀ (a : M) (b : M),
  a ∈ A → b ∈ B → dist a₀ b₀ ≤ dist a b := by
  classical
  -- Step 0: acknowledge the disjointness hypothesis for completeness.
  have _ : Disjoint A B := hAB
  -- Step 1: upgrade the non-emptiness of `A` to a `Set.Nonempty` witness.
  have hA_nonempty : A.Nonempty := by
    -- Step 1.1: rewrite using `Set.nonempty_iff_ne_empty`.
    exact Set.nonempty_iff_ne_empty.mpr hA₀
  -- Step 2: upgrade the non-emptiness of `B` to a `Set.Nonempty` witness.
  have hB_nonempty : B.Nonempty := by
    -- Step 2.1: same rewriting trick for `B`.
    exact Set.nonempty_iff_ne_empty.mpr hB₀
  -- Step 3: deduce that the Cartesian product `A ×ˢ B` is also nonempty.
  have hprod_nonempty : (A ×ˢ B).Nonempty := by
    -- Step 3.1: take the product of the two witnesses we just obtained.
    exact hA_nonempty.prod hB_nonempty
  -- Step 4: note that the map `p ↦ dist p.1 p.2` is globally continuous.
  have hdist_cont :
      Continuous fun p : M × M => dist p.1 p.2 := by
    -- Step 4.1: apply continuity of projections together with `continuous_dist`.
    simpa using (continuous_fst.dist continuous_snd)
  -- Step 5: use compactness of `A ×ˢ B` to extract a minimizer for the distance function.
  obtain ⟨p, hp, hpmin⟩ :=
    (hA.prod hB).exists_isMinOn hprod_nonempty hdist_cont.continuousOn
  -- Step 6: unpack that the chosen pair actually lies in `A ×ˢ B`.
  rcases hp with ⟨hpA, hpB⟩
  -- Step 7: package the witnesses and prove the minimality property.
  refine ⟨p.1, p.2, hpA, hpB, ?_⟩
  -- Step 7.1: fix arbitrary `a ∈ A` and `b ∈ B`.
  intro a b ha hb
  -- Step 7.2: register that the pair `(a, b)` indeed belongs to `A ×ˢ B`.
  have hab : a ∈ A ∧ b ∈ B := And.intro ha hb
  -- Step 7.2.1: use the characterization of membership in a Cartesian product.
  have hmem : (⟨a, b⟩ : M × M) ∈ A ×ˢ B := Set.mem_prod.mpr hab
  -- Step 7.3: invoke minimality and convert the statement to the desired inequality.
  simpa using hpmin hmem
