import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Show that if $X$ has a countable dense subset, every collection of disjoint open sets in $X$ is countable.
-/

/-Informal Proof

Let $\mathcal{U}$ be a collection of disjoint open sets in $X$ and let $A$ be a countable dense subset of $X$.
Since $A$ is dense in $X$, every $U \in \mathcal{U}$ intersects $S$. Therefore, there exists a point $x_U \in U \cap S$.
Let $U_1, U_2 \in \mathcal{U}, U_1 \neq U_2$. Then $x_{U_1} \neq x_{U_2}$ since $U_1 \cap U_2=\emptyset$.
Thus, the function $\mathcal{U} \rightarrow S$ given by $U \mapsto x_U$ is injective and therefore, since $S$ is countable, it follows that $\mathcal{U}$ is countable.
-/

theorem Munkres_exercise_30_13 {X : Type*} [TopologicalSpace X]
  (h : ∃ (s : Set X), Countable s ∧ Dense s) (U : Set (Set X))
  (hU : ∀ (x y : Set X), x ∈ U → y ∈ U → x ≠ y → x ∩ y = ∅)
  (hUopen : ∀ (u : Set X), u ∈ U → IsOpen u) :
  Countable U := by
  -- Step 1: Switch to classical logic so that we may freely use choice and excluded middle.
  classical
  -- Step 1.1: Unpack the countable dense subset promised by the hypothesis `h`.
  obtain ⟨s, hsCountable, hsDense⟩ := h
  -- Step 2: Show that every nonempty open set from `U` meets the dense set `s`.
  have hMem :
      ∀ {u : Set X}, u ∈ U → Set.Nonempty u → ∃ x ∈ s, x ∈ u := by
    -- Step 2.1: Fix an arbitrary member `u` of `U` that is nonempty.
    intro u huU hnonempty
    -- Step 2.2: Apply density to the open set to obtain a point simultaneously in `s` and `u`.
    obtain ⟨x, hx_s, hx_u⟩ :=
      hsDense.exists_mem_open (hUopen u huU) hnonempty
    -- Step 2.3: Return the point together with the required membership data.
    exact ⟨x, hx_s, hx_u⟩
  -- Step 3: Prepare to work with the subtype of nonempty members of `U` by selecting witnesses in `s`.
  have hMemSubtype :
      ∀ u : {u : Set X // u ∈ U ∧ Set.Nonempty u},
        ∃ x : {x : X // x ∈ s}, ((x : X) ∈ (u : Set X)) := by
    -- Step 3.1: Fix an arbitrary nonempty member `u` of the collection.
    intro u
    -- Step 3.2: Extract the facts that `u` belongs to `U` and is nonempty.
    have huU : (u : Set X) ∈ U := (u.property).1
    have huNonempty : Set.Nonempty (u : Set X) := (u.property).2
    -- Step 3.3: Use the helper from Step 2 to choose a point of `s` lying inside `u`.
    obtain ⟨x, hx_s, hx_u⟩ := hMem (u := (u : Set X)) huU huNonempty
    -- Step 3.4: Package the chosen point as an element of the subtype over `s`.
    exact ⟨⟨x, hx_s⟩, by simpa using hx_u⟩
  -- Step 4: Use choice to obtain a concrete selector sending each nonempty member to a point in `s`.
  choose pick hpick using hMemSubtype
  -- Step 5: Prove that the selector is injective, relying on the disjointness hypothesis.
  have hpick_inj : Function.Injective pick := by
    -- Step 5.1: Compare two members `u` and `v` whose chosen points coincide.
    intro u v huv
    -- Step 5.2: Record the memberships of the chosen point in `u` and `v`.
    have huMem : ((pick u : X)) ∈ (u : Set X) := hpick u
    have hvMem : ((pick u : X)) ∈ (v : Set X) := by simpa [huv] using hpick v
    -- Step 5.3: Thus the intersection of `u` and `v` is nonempty.
    have hIntersection : ((u : Set X) ∩ (v : Set X)).Nonempty :=
      ⟨(pick u : X), ⟨huMem, hvMem⟩⟩
    -- Step 5.4: Show their underlying sets must be equal; otherwise disjointness is violated.
    have hEqSets : (u : Set X) = (v : Set X) := by
      -- Step 5.4.1: Suppose for contradiction that the sets differ.
      by_contra hne
      -- Step 5.4.2: Distinct members of `U` are disjoint by hypothesis.
      have hdisj := hU (u : Set X) (v : Set X) (u.property).1 (v.property).1 hne
      -- Step 5.4.3: Extract a concrete point from the intersection to contradict emptiness.
      rcases hIntersection with ⟨z, hz⟩
      -- Step 5.4.4: The disjointness equality forces this point to lie in the empty set.
      simp [hdisj] at hz
    -- Step 5.5: Equality of underlying sets implies equality of subtypes.
    apply Subtype.ext
    -- Step 5.5.1: Conclude the two members are identical.
    simpa using hEqSets
  -- Step 6: Transfer countability of `s` to its subtype so that we can enumerate `s`.
  haveI : Countable ↥s := hsCountable
  -- Step 6.1: Obtain an explicit injection from the subtype into the natural numbers.
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat (α := ↥s)
  -- Step 6.2: Compose the selector with this injection to count the subtype of nonempty members.
  have hcountSubtype : Countable {u : Set X // u ∈ U ∧ Set.Nonempty u} := by
    -- Step 6.2.1: Provide the injection witnessing countability.
    refine ⟨⟨fun u => g (pick u), ?_⟩⟩
    -- Step 6.2.2: Injectivity follows from the injectivity of each component.
    exact hg.comp hpick_inj
  -- Step 7: Convert the type-level result into a statement about the corresponding set of nonempty members.
  set nonemptyMembers : Set (Set X) := {u | u ∈ U ∧ Set.Nonempty u}
  have hcountNonemptyMembers : nonemptyMembers.Countable := by
    -- Step 7.1: First view countability on the subtype and then pass to the set itself.
    have : Countable ↥nonemptyMembers := by
      simpa [nonemptyMembers] using hcountSubtype
    -- Step 7.2: Convert back to the `Set.Countable` formulation.
    exact Countable.to_set this
  -- Step 8: Add the (possible) empty set while preserving countability.
  set emptySingleton : Set (Set X) := ({∅} : Set (Set X))
  have hSingleton : emptySingleton.Countable := by
    simp [emptySingleton]
  have hcountUnion : (emptySingleton ∪ nonemptyMembers).Countable :=
    hSingleton.union hcountNonemptyMembers
  -- Step 9: Check that every element of `U` belongs to this countable superset.
  have hUsubset : U ⊆ emptySingleton ∪ nonemptyMembers := by
    -- Step 9.1: Start with an arbitrary member `u` of `U`.
    intro u huU
    -- Step 9.2: Separate into whether `u` is empty or not.
    by_cases hNonempty : Set.Nonempty u
    · -- Step 9.2.1: Nonempty members fall into `nonemptyMembers` directly.
      exact Or.inr ⟨huU, hNonempty⟩
    · -- Step 9.2.2: Otherwise, `u` must equal the empty set.
      have hEmpty : u = (∅ : Set X) := by
        simpa [Set.not_nonempty_iff_eq_empty] using hNonempty
      -- Step 9.2.3: Hence `u` lies in the singleton `{∅}`.
      have : u ∈ emptySingleton := by
        simp [emptySingleton, Set.mem_singleton_iff, hEmpty]
      exact Or.inl this
  -- Step 10: Finally, restrict the countable superset back down to `U`.
  exact (Set.Countable.mono hUsubset) hcountUnion

