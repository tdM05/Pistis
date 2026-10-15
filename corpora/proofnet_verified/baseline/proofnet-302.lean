import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Let $\left\{A_{\alpha}\right\}$ be a collection of connected subspaces of $X$; let $A$ be a connected subset of $X$. Show that if $A \cap A_{\alpha} \neq \varnothing$ for all $\alpha$, then $A \cup\left(\bigcup A_{\alpha}\right)$ is connected.
-/

/-Informal Proof

For each $\alpha$ we have $A \cap A_\alpha \neq \emptyset$, so each $A \cup A_\alpha$ is connected by Theorem 23.3. In turn $\left\{A \cup A_\alpha\right\}_\alpha$ is a collection of connected spaces that have a point in common (namely any point in $A)$, so $\bigcup_\alpha\left(A \cup A_\alpha\right)=A \cup\left(\bigcup_\alpha A_\alpha\right)$ is connected.
-/

theorem Munkres_exercise_23_3 {X α : Type*} [TopologicalSpace X]
  {A : α → Set X}
  (hAa : ∀ a, IsConnected (A a))
  (A₀ : Set X)
  (hA : IsConnected A₀)
  (h : ∀ a, A₀ ∩ A a ≠ ∅) :
  IsConnected (A₀ ∪ (⋃ a, A a)) := by
  classical
  -- Step 1: upgrade each `A₀ ∩ A a ≠ ∅` to an explicit `Nonempty` witness for later use.
  have hInter : ∀ a, (A₀ ∩ A a).Nonempty := by
    -- Step 1.1: apply the equivalence between `≠ ∅` and `Nonempty`.
    intro a
    exact (Set.nonempty_iff_ne_empty).2 (h a)
  -- Step 2: deduce that every `A₀ ∪ A a` is connected via the standard union lemma.
  have hUnionConn : ∀ a, IsConnected (A₀ ∪ A a) := by
    -- Step 2.1: apply `IsConnected.union` to each pair `(A₀, A a)`.
    intro a
    simpa using IsConnected.union (s := A₀) (t := A a) (H := hInter a) hA (hAa a)
  -- Step 3: pick a concrete point `x ∈ A₀` that will act as the common witness.
  obtain ⟨x, hxA₀⟩ := hA.nonempty
  -- Step 4: package the relevant connected sets into a single family `c`.
  set c : Set (Set X) := insert A₀ (Set.range fun a : α => A₀ ∪ A a)
  -- Step 4.1: verify that the chosen point `x` belongs to every member of `c`.
  have hx_mem : ∀ s ∈ c, x ∈ s := by
    intro s hs
    -- Step 4.1.0: expand the membership condition in `c`.
    have hs' : s = A₀ ∨ ∃ a, A₀ ∪ A a = s := by
      simpa [c] using hs
    rcases hs' with hs | hs
    · -- Step 4.1.1: the case `s = A₀` is immediate.
      simpa [hs] using hxA₀
    · -- Step 4.1.2: if `s = A₀ ∪ A a`, then `x ∈ A₀ ⊆ s`.
      rcases hs with ⟨a, hs⟩
      simpa [hs.symm] using (Or.inl hxA₀)
  -- Step 4.2: record that every element of `c` is preconnected.
  have hc_pre : ∀ s ∈ c, IsPreconnected s := by
    intro s hs
    -- Step 4.2.0: expand `s ∈ c` as before.
    have hs' : s = A₀ ∨ ∃ a, A₀ ∪ A a = s := by
      simpa [c] using hs
    rcases hs' with hs | hs
    · -- Step 4.2.1: `A₀` is preconnected because it is connected.
      simpa [hs] using hA.isPreconnected
    · -- Step 4.2.2: each `A₀ ∪ A a` is preconnected by Step 2.
      rcases hs with ⟨a, hs⟩
      simpa [hs.symm] using (hUnionConn a).isPreconnected
  -- Step 5: deduce that the big union of all sets in `c` is connected.
  have hPre : IsPreconnected (⋃₀ c) :=
    isPreconnected_sUnion x c hx_mem hc_pre
  -- Step 5.1: note that `x` actually lies in the union, giving non-emptiness.
  have hx_union : x ∈ ⋃₀ c := by
    have hA0_mem : A₀ ∈ c := by simp [c]
    exact (subset_sUnion_of_mem hA0_mem) hxA₀
  have hConn : IsConnected (⋃₀ c) := ⟨⟨x, hx_union⟩, hPre⟩
  -- Step 6: identify the target set with `⋃₀ c` via mutual inclusions.
  have hSubset_to_c : A₀ ∪ ⋃ a, A a ⊆ ⋃₀ c := by
    -- Step 6.1: handle the `A₀` part and the `⋃ a, A a` part separately.
    refine Set.union_subset ?_ ?_
    · -- Step 6.1.1: `A₀` itself is in `c`, hence contained in the union.
      exact subset_sUnion_of_mem (by simp [c])
    · -- Step 6.1.2: each `A a` sits inside `A₀ ∪ A a`, which belongs to `c`.
      refine Set.iUnion_subset ?_
      intro a
      have hmem : A₀ ∪ A a ∈ c := by
        refine Set.mem_insert_of_mem _ ?_
        exact Set.mem_range.2 ⟨a, rfl⟩
      intro y hy
      exact (subset_sUnion_of_mem hmem) (Or.inr hy)
  have hSubset_from_c : ⋃₀ c ⊆ A₀ ∪ ⋃ a, A a := by
    -- Step 6.2: unravel membership in `⋃₀ c` and split into the two constructors of `c`.
    intro y hy
    rcases Set.mem_sUnion.1 hy with ⟨s, hs, hys⟩
    have hs' : s = A₀ ∨ ∃ a, A₀ ∪ A a = s := by
      simpa [c] using hs
    rcases hs' with hs | hs
    · -- Step 6.2.1: if `s = A₀`, the element lies in `A₀`.
      exact Or.inl (by simpa [hs] using hys)
    · -- Step 6.2.2: if `s = A₀ ∪ A a`, the element is in `A₀` or some `A a`.
      rcases hs with ⟨a, hs⟩
      have hMem : y ∈ A₀ ∪ A a := by simpa [hs.symm] using hys
      rcases hMem with hMem | hMem
      · exact Or.inl hMem
      · exact Or.inr (Set.mem_iUnion.2 ⟨a, hMem⟩)
  have hEq : ⋃₀ c = A₀ ∪ ⋃ a, A a :=
    Set.Subset.antisymm hSubset_from_c hSubset_to_c
  -- Step 7: rewrite the conclusion using the identified union.
  simpa [hEq] using hConn
