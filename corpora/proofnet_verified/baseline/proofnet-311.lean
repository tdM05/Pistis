import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Show that if $X$ is a countable product of spaces having countable dense subsets, then $X$ has a countable dense subset.
-/

/-Informal Proof

Let $\left(X_n\right)$ be spaces having countable dense subsets $\left(A_n\right)$. For each $n$, fix an arbitrary $x_n \in X_n$. Consider the subset $A$ of $X$ defined by
$$
A=\bigcup\left\{\prod U_n: U_n=A_n \text { for finitely many } n \text { and is }\left\{x_n\right\} \text { otherwise }\right\} .
$$
This set is countable because the set of finite subsets of $\mathbb{N}$ is countable and each of the inner sets is countable. Now, let $x \in X$ and $V=\prod V_n$ be a basis element containing $x$ such that each $V_n$ is open in $X_n$ and $V_n=X_n$ for all but finitely many $n$. For each $n$, if $V_n \neq X_n$, choose a $y_n \in\left(A_n \cap V_n\right)$ (such a $y_n$ exists since $A_n$ is dense in $\left.X_n\right)$. Otherwise, let $y_n=x_n$. Then $\left(y_n\right) \in(A \cap V)$, proving that $A$ is dense in $X$.
-/

theorem Munkres_exercise_30_10
  {X : ℕ → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, ∃ (s : Set (X i)), Countable s ∧ Dense s) :
  ∃ (s : Set (Π i, X i)), Countable s ∧ Dense s := by
  classical
  -- Step 1: Extract for every coordinate a countable dense subset from the hypothesis `h`.
  choose s hs using h
  -- Step 1.1: Keep track of the countability information of each chosen subset `s i`.
  have hs_count : ∀ i, (s i).Countable := fun i => (hs i).1
  -- Step 1.2: Keep track of the density information of each chosen subset `s i`.
  have hs_dense : ∀ i, Dense (s i) := fun i => (hs i).2
  -- Step 2: Split into the case where the product is inhabited and the case where it is empty.
  by_cases hprod : Nonempty (Π i, X i)
  · -- Step 2.1: Fix a base point `x₀` in the product to serve as the default value outside finitely many coordinates.
    obtain ⟨x₀⟩ := hprod
    -- Step 2.2: Prepare a helper that extends finite selections of coordinates into full functions.
    let extend : ∀ t : Finset ℕ, (∀ i : {j // j ∈ t}, X i.1) → Π i, X i :=
      fun t g i => if hi : i ∈ t then g ⟨i, hi⟩ else x₀ i
    -- Step 2.3: For each finite set `t`, collect the functions that differ from `x₀` only on `t` and take values inside the dense sets there.
    let B : Finset ℕ → Set (Π i, X i) := fun t =>
      (fun g : (∀ i : {j // j ∈ t}, X i.1) => extend t g) ''
        Set.pi Set.univ (fun i : {j // j ∈ t} => s i.1)
    -- Step 2.4: Define the global candidate set `A` as the union over all finite supports.
    let A : Set (Π i, X i) := ⋃ t : Finset ℕ, B t
    -- Step 2.5: Prove that each block `B t` is countable by mapping a countable `Set.pi` via `extend`.
    have hB_count : ∀ t : Finset ℕ, (B t).Countable := by
      intro t
      -- Step 2.5.1: Show the domain `Set.pi` is countable using the finiteness of `t`.
      have hpi :
          (Set.pi Set.univ fun i : {j // j ∈ t} => s i.1).Countable := by
        -- Step 2.5.1.1: The index subtype `{j // j ∈ t}` is finite because `t` is finite.
        haveI : Finite {j // j ∈ t} := by
          classical
          simpa [Finset.mem_coe] using (t.finite_toSet.to_subtype)
        -- Step 2.5.1.2: Apply `countable_univ_pi` with the known countability of every `s i`.
        simpa using countable_univ_pi (fun i : {j // j ∈ t} => hs_count i.1)
      -- Step 2.5.2: Images of countable sets are countable, so `B t` is countable.
      exact hpi.image _
    -- Step 2.6: Use the countable union of countable sets to see that `A` is countable.
    have hA_count : A.Countable :=
      countable_iUnion (fun t : Finset ℕ => hB_count t)
    -- Step 2.7: Prove that `A` is dense by intersecting it with every basic neighborhood.
    have hA_dense : Dense A := by
      -- Step 2.7.1: Reduce density to the non-emptiness of intersections with arbitrary non-empty open sets.
      refine (dense_iff_inter_open).2 ?_
      intro U hU_open hU_nonempty
      -- Step 2.7.2: Pick a witness point `x` in `U`.
      rcases hU_nonempty with ⟨x, hxU⟩
      -- Step 2.7.3: Shrink `U` to a basic product neighborhood `(F : Set ℕ).pi W` using the product basis.
      obtain ⟨V, ⟨W, F, hW, rfl⟩, hxV, hV_subset⟩ :=
        (isTopologicalBasis_pi fun _ : ℕ => isTopologicalBasis_opens).exists_subset_of_mem_open
          hxU hU_open
      -- Step 2.7.4: Record the coordinate-wise membership of `x` in that basic neighborhood.
      have hx_coords : ∀ i ∈ F, x i ∈ W i := by
        simpa [Set.mem_pi, Finset.mem_coe] using hxV
      -- Step 2.7.5: For each restricted coordinate, pick a point from the dense set inside the chosen open slice.
      have hy_exists : ∀ i ∈ F, ∃ y : X i, y ∈ s i ∧ y ∈ W i := by
        intro i hi
        have hWi_open : IsOpen (W i) := hW i hi
        have hWi_nonempty : (W i).Nonempty := ⟨x i, hx_coords i hi⟩
        obtain ⟨y, hyS, hyW⟩ := (hs_dense i).exists_mem_open hWi_open hWi_nonempty
        exact ⟨y, hyS, hyW⟩
      -- Step 2.7.6: Use choice to assemble those finite selections into a function on `{j // j ∈ F}`.
      choose y hy_mem_s hy_mem_W using hy_exists
      -- Step 2.7.7: Package the selections as a function `g` on the subtype index.
      let g : ∀ i : {j // j ∈ F}, X i.1 := fun i => y i.1 i.2
      -- Step 2.7.8: Verify that `g` indeed belongs to the `Set.pi` describing the domain of `B F`.
      have g_mem :
          g ∈ Set.pi Set.univ (fun i : {j // j ∈ F} => s i.1) := by
        classical
        simp [g, Set.mem_pi, hy_mem_s]
      -- Step 2.7.9: Extend `g` back to the whole product using `extend` and note that the result lives in `B F ⊆ A`.
      let z := extend F g
      have hz_in_component : z ∈ B F := by
        refine ⟨g, g_mem, rfl⟩
      have hzA : z ∈ A := by
        refine mem_iUnion.2 ?_
        exact ⟨F, hz_in_component⟩
      -- Step 2.7.10: Check that `z` actually lies inside the basic neighborhood `(F : Set ℕ).pi W`.
      have hzV_aux : ∀ i ∈ F, z i ∈ W i := by
        intro i hi
        classical
        simp [z, extend, hi, g, hy_mem_W i hi]
      have hzV : z ∈ (F : Set ℕ).pi W := by
        simpa [Set.mem_pi, Finset.mem_coe] using hzV_aux
      -- Step 2.7.11: Combine the membership facts to obtain a point in `U ∩ A`.
      refine ⟨z, ⟨hV_subset hzV, hzA⟩⟩
    -- Step 2.8: Collect the properties of `A` to conclude the inhabited case.
    exact ⟨A, hA_count, hA_dense⟩
  · -- Step 3: If the product is empty, use the empty set as a countable dense subset.
    have hx : ∀ x : Π i, X i, False := fun x => hprod ⟨x⟩
    -- Step 3.1: The empty set is trivially countable.
    refine ⟨(∅ : Set (Π i, X i)), Set.countable_empty, ?_⟩
    -- Step 3.2: Show the empty set is dense because the product has no points.
    have hclosure :
        closure (∅ : Set (Π i, X i)) = (Set.univ : Set (Π i, X i)) := by
      apply Set.eq_univ_iff_forall.mpr
      intro x
      exact (hx x).elim
    simpa [Dense, hclosure]
