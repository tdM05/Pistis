import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Let $A \subset X$. Show that if $C$ is a connected subspace of $X$ that intersects both $A$ and $X-A$, then $C$ intersects $\operatorname{Bd} A$.
-/

/-Informal Proof

Suppose that $C \cap B d A=C \cap \bar{A} \cap \overline{X-A}=\emptyset$. Then $C \cap A$ and $C \cap(X \backslash A)$ are a pair of disjoint non-empty sets whose union is all of $C$, neither of which contains a limit point of the other. Indeed, if $C \cap(X-A)$ contains a limit point $x$ of $C \cap A$, then $x \in C \cap(X-A) \cap A^{\prime} \subset C \cap \bar{A} \cap \overline{X-A}=\emptyset$, a contradiction, and similarly $C \cap A$ does not contain a limit point of $C \cap(X-A)$. Then $C \cap A$ and $C \cap(X-A)$ constitute a separation of $C$, contradicting the fact that $C$ is connected (Lemma 23.1).
-/

theorem Munkres_exercise_23_6 {X : Type*}
  [TopologicalSpace X] {A C : Set X} (hc : IsConnected C)
  (hCA : C ∩ A ≠ ∅) (hCXA : C ∩ Aᶜ ≠ ∅) :
  C ∩ (frontier A) ≠ ∅ := by
  classical
  -- Step 1: Argue by contradiction and assume that `C` misses the boundary of `A`.
  by_contra hFront
  -- Step 2: Name the open pieces cut out by `A` and its complement.
  set U := interior A with hUdef
  set V := interior (Aᶜ) with hVdef
  have hUopen : IsOpen U := by
    simp [U]
  have hVopen : IsOpen V := by
    simp [V]
  -- Step 3: Record that `U` and `V` are disjoint because they live inside complementary sets.
  have hUVempty : U ∩ V = (∅ : Set X) := by
    refine Set.Subset.antisymm ?_ (Set.empty_subset _)
    intro x hx
    rcases hx with ⟨hxU, hxV⟩
    have hxA : x ∈ A := by
      have : x ∈ interior A := by simpa [U] using hxU
      exact interior_subset this
    have hxAc : x ∈ Aᶜ := by
      have : x ∈ interior (Aᶜ) := by simpa [V] using hxV
      exact interior_subset this
    exact (hxAc hxA).elim
  -- Step 4: Show that every point of `C` must belong to `U ∪ V`; otherwise we get a boundary point.
  have hCover : C ⊆ U ∪ V := by
    intro x hxC
    by_contra hxUV
    have hxNotU : x ∉ U := fun hx => hxUV (Or.inl hx)
    have hxNotV : x ∉ V := fun hx => hxUV (Or.inr hx)
    have hxClosureA : x ∈ closure A := by
      have hxMem : x ∈ (interior (Aᶜ))ᶜ := by
        simpa [V] using hxNotV
      convert hxMem using 1
      exact closure_eq_compl_interior_compl (s := A)
    have hxNotIntA : x ∉ interior A := by
      simpa [U] using hxNotU
    have hxFrontier : x ∈ frontier A := by
      change x ∈ closure A \ interior A
      exact ⟨hxClosureA, hxNotIntA⟩
    have hxCF : x ∈ C ∩ frontier A := ⟨hxC, hxFrontier⟩
    simp [hFront] at hxCF
  -- Step 5: Extract a concrete point of `C ∩ U` using the assumption `C ∩ A ≠ ∅`.
  have hCIntU : (C ∩ U).Nonempty := by
    obtain ⟨x, hxC, hxA⟩ := Set.nonempty_iff_ne_empty.2 hCA
    have hxU : x ∈ U := by
      by_contra hxNotU
      have hxNotInt : x ∉ interior A := by simpa [U] using hxNotU
      have hxClosureA : x ∈ closure A := subset_closure hxA
      have hxFrontier : x ∈ frontier A := by
        change x ∈ closure A \ interior A
        exact ⟨hxClosureA, hxNotInt⟩
      have hxCF : x ∈ C ∩ frontier A := ⟨hxC, hxFrontier⟩
      simp [hFront] at hxCF
    refine ⟨x, ?_⟩
    exact ⟨hxC, hxU⟩
  -- Step 6: Do the same on the complementary side to obtain a point of `C ∩ V`.
  have hCIntV : (C ∩ V).Nonempty := by
    obtain ⟨x, hxC, hxAc⟩ := Set.nonempty_iff_ne_empty.2 hCXA
    have hxV : x ∈ V := by
      by_contra hxNotV
      have hxClosureA : x ∈ closure A := by
        have hxMem : x ∈ (interior (Aᶜ))ᶜ := by
          simpa [V] using hxNotV
        convert hxMem using 1
        exact closure_eq_compl_interior_compl (s := A)
      have hxNotIntA : x ∉ interior A := by
        intro hxIntA
        have : x ∈ A := interior_subset hxIntA
        exact hxAc this
      have hxFrontier : x ∈ frontier A := by
        change x ∈ closure A \ interior A
        exact ⟨hxClosureA, hxNotIntA⟩
      have hxCF : x ∈ C ∩ frontier A := ⟨hxC, hxFrontier⟩
      simp [hFront] at hxCF
    refine ⟨x, ?_⟩
    exact ⟨hxC, hxV⟩
  -- Step 7: Apply preconnectedness of `C` to the open cover `U ∪ V` and derive a contradiction.
  have hIntersect :=
    hc.isPreconnected U V hUopen hVopen hCover hCIntU hCIntV
  have hContr : False := by
    simp [hUVempty] at hIntersect
  exact hContr
