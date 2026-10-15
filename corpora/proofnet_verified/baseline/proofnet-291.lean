import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

/-Informal Statement

Let $\mathcal{T}_\alpha$ be a family of topologies on $X$. Show that there is a unique largest topology on $X$ contained in all the collections $\mathcal{T}_\alpha$.
-/

/-Informal Proof

Now we prove that there exists a unique largest topology contained in all $\mathcal{T}_\alpha$. Uniqueness of such topology is clear. Consider $\mathcal{T}=\bigcap_\alpha \mathcal{T}_\alpha$. We already know that $\mathcal{T}$ is a topology by, and clearly $\mathcal{T} \subset \mathcal{T}_\alpha$ for all $\alpha$. If $\mathcal{O}$ is another topology contained in all $\mathcal{T}_\alpha$, it must be contained in their intersection, so $\mathcal{O} \subset \mathcal{T}$. I follows that $\mathcal{T}$ is the unique largest topology contained in all $\mathcal{T}_\alpha$.
-/

theorem Munkres_exercise_13_4b2 (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  classical
  -- Step 1: Introduce the candidate topology T' consisting of all sets that live in every T i.
  let T' : Set (Set X) := {U | ∀ i, U ∈ T i}
  -- Step 2: Show that every element of T' automatically belongs to each T i (obvious inclusion direction).
  have h_subset : ∀ i, T' ⊆ T i := by
    -- Step 2.1: Fix an index i and a set U that lies in T'.
    intro i U hU
    -- Step 2.2: Unfold the definition of T' to conclude that U ∈ T i.
    exact hU i
  -- Step 3: Prove that the candidate T' satisfies the three axioms of a topology.
  have h_top : is_topology X T' := by
    -- Step 3.1: Unpack the three topology axioms (universe, finite intersections, arbitrary unions).
    refine ⟨?univ, ?intersections, ?unions⟩
    -- Step 3.1.1: univ belongs to every T i, hence also to T'.
    · -- Step 3.1.1.1: Membership in T' demands belonging to each T i.
      intro i
      -- Step 3.1.1.2: Extract univ ∈ T i from the given topology structure on T i.
      exact (h i).1
    -- Step 3.1.2: T' is closed under finite intersections.
    · -- Step 3.1.2.1: Take sets s and t in T' and show their intersection is still in T'.
      intro s t hs ht i
      -- Step 3.1.2.2: Since s and t sit in every T i, use closure of T i under intersections.
      have hs_i : s ∈ T i := hs i
      have ht_i : t ∈ T i := ht i
      -- Step 3.1.2.3: Apply the topology axiom for finite intersections inside T i.
      exact (h i).2.1 s t hs_i ht_i
    -- Step 3.1.3: T' is closed under arbitrary unions.
    · -- Step 3.1.3.1: Assume every member of S lies in T'; prove that the union lies in T'.
      intro S hS i
      -- Step 3.1.3.2: Build the hypothesis that every member of S lies in T i.
      have hS_i : ∀ t ∈ S, t ∈ T i := by
        -- Step 3.1.3.2.1: Any t ∈ S is in T', so it is also in each T i.
        intro t ht
        exact (hS t ht) i
      -- Step 3.1.3.3: Invoke closure of T i under arbitrary unions.
      exact (h i).2.2 S hS_i
  -- Step 4: Encode the maximality property required in the statement (largest topology contained in all T i).
  have h_max : ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
    -- Step 4.1: Fix a topology T'' that sits inside every T i.
    intro T'' hT'' hsubset'' U hU i
    -- Step 4.2: Membership in T' is equivalent to membership in every T i, so conclude using the inclusions.
    exact hsubset'' i hU
  -- Step 5: Package existence together with the recorded properties of T'.
  refine ⟨T', ?_, ?_⟩
  -- Step 5.1: Provide the tuple (is_topology, inclusions, maximality) demanded in the specification.
  · exact ⟨h_top, h_subset, h_max⟩
  -- Step 5.2: Prove uniqueness by showing any other candidate agrees with T'.
  · intro S hS
    -- Step 5.2.1: Break the hypothesis on S into its three components.
    rcases hS with ⟨hS_top, hS_subset, hS_max⟩
    -- Step 5.2.2: Establish equality via mutual subset inclusions.
    apply Set.Subset.antisymm
    -- Step 5.2.2.1: S ⊆ T' because T' is the largest topology with the constraint.
    · exact h_max S hS_top hS_subset
    -- Step 5.2.2.2: T' ⊆ S because S also satisfies the universal property.
    · exact hS_max T' h_top h_subset
