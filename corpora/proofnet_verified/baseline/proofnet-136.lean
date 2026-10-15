import Mathlib

open Filter Real Function
open scoped Topology



/-Informal Statement

Let $\mathcal{T}$ be the collection of open subsets of a metric space $\mathrm{M}$, and $\mathcal{K}$ the collection of closed subsets. Show that there is a bijection from $\mathcal{T}$ onto $\mathcal{K}$.
-/

/-Informal Proof

The bijection given by $x\mapsto X^C$ suffices.
-/

theorem Pugh_exercise_2_29 (M : Type*) [MetricSpace M]
  (O C : Set (Set M))
  (hO : O = {s | IsOpen s})
  (hC : C = {s | IsClosed s}) :
  ∃ f : O → C, Bijective f := by
  classical
  -- Step 1: rewrite membership in `O` and `C` as the standard openness/closedness predicates.
  have hOmem : ∀ {U : Set M}, U ∈ O ↔ IsOpen U := by
    intro U
    -- Step 1.1: reduce membership to the set-builder description supplied by `hO`.
    simp [hO]
  have hCmem : ∀ {U : Set M}, U ∈ C ↔ IsClosed U := by
    intro U
    -- Step 1.2: reduce membership to the set-builder description supplied by `hC`.
    simp [hC]
  -- Step 2: define the forward complement map from open sets to closed sets.
  let f : O → C := fun o =>
    ⟨o.1ᶜ, by
      -- Step 2.1: the complement of an open set is closed, so it belongs to `C`.
      have hOpen : IsOpen o.1 := (hOmem).mp o.property
      have hClosed : IsClosed o.1ᶜ := (isClosed_compl_iff).2 hOpen
      exact (hCmem).mpr hClosed⟩
  -- Step 3: define the reverse complement map from closed sets to open sets.
  let g : C → O := fun c =>
    ⟨c.1ᶜ, by
      -- Step 3.1: the complement of a closed set is open, so it belongs to `O`.
      have hClosed : IsClosed c.1 := (hCmem).mp c.property
      have hOpen : IsOpen c.1ᶜ := (isOpen_compl_iff).2 hClosed
      exact (hOmem).mpr hOpen⟩
  -- Step 4: prove that `g` composed with `f` returns the original open set (double complement).
  have h_left : Function.LeftInverse g f := by
    -- Step 4.1: extensionality reduces the claim to pointwise membership, then double complements.
    intro o
    ext x
    -- Step 4.1.1: simplify the membership statements using the explicit descriptions of `f` and `g`.
    simp [f, g]
  -- Step 5: prove that `f` composed with `g` returns the original closed set (double complement).
  have h_right : Function.RightInverse g f := by
    -- Step 5.1: the argument mirrors Step 4, now starting from an arbitrary closed set.
    intro c
    ext x
    -- Step 5.1.1: once again, simplification rests on the involutive nature of complements.
    simp [f, g]
  -- Step 6: package the constructed map together with the bijectivity facts obtained above.
  refine ⟨f, ?_⟩
  -- Step 6.1: a left inverse yields injectivity, and a right inverse yields surjectivity.
  exact ⟨h_left.injective, h_right.surjective⟩
