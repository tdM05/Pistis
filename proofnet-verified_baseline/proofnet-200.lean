import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators



/-Informal Statement

Prove that the union of two subspaces of $V$ is a subspace of $V$ if and only if one of the subspaces is contained in the other.
-/

/-Informal Proof

To prove this one way, suppose for purposes of contradiction that for $U_1$ and $U_2$, which are subspaces of $V$, that $U_1 \cup U_2$ is a subspace and neither is completely contained within the other. In other words, $U_1 \nsubseteq U_2$ and $U_2 \nsubseteq U_1$. We will show that you can pick a vector $v \in U_1$ and a vector $u \in U_2$ such that $v+u \notin U_1 \cup U_2$, proving that if $U_1 \cup U_2$ is a subspace, one must be completely contained inside the other.

If $U_1 \nsubseteq U_2$, we can pick a $v \in U_1$ such that $v \notin U_2$. Since $v$ is in the subspace $U_1$, then $(-v)$ must also be, by definition. Similarly, if $U_2 \nsubseteq U_1$, then we can pick a $u \in U_2$ such that $u \notin U_1$. Since $u$ is in the subspace $U_2$, then $(-u)$ must also be, by definition.

If $v+u \in U_1 \cup U_2$, then $v+u$ must be in $U_1$ or $U_2$. But, $v+u \in U_1 \Rightarrow v+u+(-v) \in U_1 \Rightarrow u \in U_1$
Similarly,
$$
v+u \in U_2 \Rightarrow v+u+(-u) \in U_2 \Rightarrow v \in U_2
$$
This is clearly a contradiction, as each element was defined to not be in these subspaces. Thus our initial assumption must have been wrong, and $U_1 \subseteq U_2$ or $U_2 \subseteq U_1$
To prove the other way, Let $U_1 \subseteq U_2$ (WLOG). $U_1 \subseteq U_2 \Rightarrow U_1 \cup U_2=U_2$. Since $U_2$ is a subspace, $U_1 \cup U_2$ is as well. QED.
-/

theorem Axler_exercise_1_9 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] (U W : Submodule F V):
  (∃ U' : Submodule F V, U'.carrier = ↑U ∪ ↑W) ↔ (U ≤ W ∨ W ≤ U) := by
  classical
  constructor
  · -- Step 1: Assume there exists a submodule realizing the union and deduce the comparability.
    rintro ⟨U', hU'⟩
    -- Step 1.1: Suppose, for contradiction, that neither inclusion holds.
    by_contra h
    -- Step 1.2: Record the two explicit failures of inclusion.
    have hnot : ¬ U ≤ W ∧ ¬ W ≤ U := not_or.1 h
    have hU_notle : ¬ U ≤ W := hnot.1
    have hW_notle : ¬ W ≤ U := hnot.2
    -- Step 1.3: Extract elements witnessing each failed inclusion.
    obtain ⟨u, huU, huW⟩ :
        ∃ u, u ∈ U ∧ u ∉ W := by
      -- Step 1.3.1: If no such u existed, then U would be contained in W, contradicting hU_notle.
      by_contra hnone
      have h_le : U ≤ W := by
        intro x hx
        classical
        by_contra hxW
        exact hnone ⟨x, hx, hxW⟩
      exact hU_notle h_le
    obtain ⟨w, hwW, hwU⟩ :
        ∃ w, w ∈ W ∧ w ∉ U := by
      -- Step 1.3.2: Apply the symmetric argument for the other inclusion.
      by_contra hnone
      have h_le : W ≤ U := by
        intro x hx
        classical
        by_contra hxU
        exact hnone ⟨x, hx, hxU⟩
      exact hW_notle h_le
    -- Step 1.4: Relate set-theoretic membership with the witness submodule via the carrier equality.
    have hUnion :
        ∀ {x}, x ∈ U' ↔ x ∈ U ∨ x ∈ W := by
      intro x
      constructor
      · -- Step 1.4.0a: From U' to the set-theoretic union.
        intro hx
        have hx_carrier := hx
        change x ∈ U'.carrier at hx_carrier
        have hx_eq := congrArg (fun s : Set V => x ∈ s) hU'
        have hx_union : x ∈ (↑U : Set V) ∪ (↑W : Set V) :=
          Eq.mp hx_eq hx_carrier
        simpa using hx_union
      · -- Step 1.4.0b: From the union back to U'.
        intro hx
        have hx_union : x ∈ (↑U : Set V) ∪ (↑W : Set V) := by
          change x ∈ (↑U : Set V) ∪ (↑W : Set V)
          simpa using hx
        have hx_eq := congrArg (fun s : Set V => x ∈ s) hU'.symm
        have hx_carrier : x ∈ U'.carrier := Eq.mp hx_eq hx_union
        simpa using hx_carrier
    have h_mem_union_of_memU' :
        ∀ {x}, x ∈ U' → x ∈ U ∨ x ∈ W := by
      intro x hx
      exact (hUnion (x := x)).1 hx
    have h_memU'_of_union :
        ∀ {x}, (x ∈ U ∨ x ∈ W) → x ∈ U' := by
      intro x hx
      exact (hUnion (x := x)).2 hx
    -- Step 1.4.1: Deduce that every element of U (resp. W) is inside U'.
    have h_mem_of_memU :
        ∀ {x}, x ∈ U → x ∈ U' := by
      intro x hx
      exact h_memU'_of_union (Or.inl hx)
    have h_mem_of_memW :
        ∀ {x}, x ∈ W → x ∈ U' := by
      intro x hx
      exact h_memU'_of_union (Or.inr hx)
    -- Step 1.5: Use closure of U' to deduce that u + w lies in the set-theoretic union.
    have huU' : u ∈ U' := h_mem_of_memU huU
    have hwU' : w ∈ U' := h_mem_of_memW hwW
    have hsumU' : u + w ∈ U' := U'.add_mem huU' hwU'
    change (u + w) ∈ U'.carrier at hsumU'
    have hsum_union : u + w ∈ U ∨ u + w ∈ W :=
      h_mem_union_of_memU' hsumU'
    -- Step 1.6: Perform a case split on the union membership and reach a contradiction in each branch.
    rcases hsum_union with hsumU | hsumW
    · -- Step 1.6.1: If u + w belongs to U, deduce that w also lies in U.
      have hsumU' : u + w ∈ U := by
        simpa using hsumU
      have hw_in_U : w ∈ U := by
        have : (u + w) + (-u) ∈ U :=
          U.add_mem hsumU' (U.neg_mem huU)
        simpa [add_comm, add_left_comm, add_assoc] using this
      exact (hwU hw_in_U)
    · -- Step 1.6.2: If u + w belongs to W, deduce that u also lies in W.
      have hsumW' : u + w ∈ W := by
        simpa using hsumW
      have hu_in_W : u ∈ W := by
        have : (u + w) + (-w) ∈ W :=
          W.add_mem hsumW' (W.neg_mem hwW)
        simpa [add_comm, add_left_comm, add_assoc] using this
      exact (huW hu_in_W)
  · -- Step 2: Starting from a comparability assumption, explicitly construct the submodule.
    intro h
    -- Step 2.1: Split into the two possible inclusion cases.
    cases h with
    | inl hUW =>
        -- Step 2.1.1: When U ≤ W, the union is just W.
        refine ⟨W, ?_⟩
        -- Step 2.1.2: Show the underlying sets satisfy ↑W = ↑U ∪ ↑W.
        have hsubset : (↑U : Set V) ⊆ (↑W : Set V) := by
          intro x hx
          have : x ∈ W := hUW hx
          simpa using this
        -- Step 2.1.3: Apply the set-theoretic lemma to finish this branch.
        simpa using (Set.union_eq_right.mpr hsubset).symm
    | inr hWU =>
        -- Step 2.2.1: When W ≤ U, the union is just U.
        refine ⟨U, ?_⟩
        -- Step 2.2.2: Show ↑U contains ↑W, so it equals their union.
        have hsubset : (↑W : Set V) ⊆ (↑U : Set V) := by
          intro x hx
          have : x ∈ U := hWU hx
          simpa using this
        -- Step 2.2.3: Apply the symmetric set-theoretic lemma.
        simpa using (Set.union_eq_left.mpr hsubset).symm
