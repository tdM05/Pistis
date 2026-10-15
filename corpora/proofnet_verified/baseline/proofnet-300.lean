import Mathlib

open Filter Set TopologicalSpace Topology



/-Informal Statement

Let $p: X \rightarrow Y$ be a continuous map. Show that if there is a continuous map $f: Y \rightarrow X$ such that $p \circ f$ equals the identity map of $Y$, then $p$ is a quotient map.
-/

/-Informal Proof

Let $1_Y: Y \rightarrow Y$ be the identity map in $Y$. If $U$ is a subset of $Y$ and $p^{-1}(U)$ is open in $X$, then $f^{-1}\left(p^{-1}(U)\right)=1_Y^{-1}(U)=U$ is open in $Y$ by continuity of $f$. Thus $p$ is a quotient map.
-/

theorem Munkres_exercise_22_2a {X Y : Type*} [TopologicalSpace X]
  [TopologicalSpace Y] (p : X → Y) (h : Continuous p) :
  (∃ (f : Y → X), Continuous f ∧ p ∘ f = id) → IsQuotientMap p := by
  -- Step 0: Activate classical logic so we can freely use function extensionality lemmas.
  classical
  -- Step 1: Introduce the existence of a continuous right inverse for `p`.
  intro hf
  -- Step 1.1: Extract the specific map `f` together with its continuity and right-inverse equation.
  rcases hf with ⟨f, hf_cont, hf_comp⟩
  -- Step 1.2: Record the pointwise form `p (f y) = y`, which follows from `p ∘ f = id`.
  have hf_pointwise : ∀ y, p (f y) = y := by
    -- Step 1.2.1: Evaluate the functional equality at an arbitrary point `y`.
    intro y
    -- Step 1.2.2: Simplify the compositions to obtain the desired identity.
    have := congrArg (fun g : Y → Y => g y) hf_comp
    simpa [Function.comp] using this
  -- Step 2: Deduce that `p` is surjective by using the explicit preimage `f y` of each `y`.
  have h_surj : Function.Surjective p := by
    -- Step 2.1: For any `y`, exhibit `f y` as a preimage whose image is `y`.
    intro y
    exact ⟨f y, hf_pointwise y⟩
  -- Step 3: Show that the topology on `Y` coincides with the coinduced topology via `p`.
  have h_eq_coinduced :
      (inferInstance : TopologicalSpace Y) =
        (inferInstance : TopologicalSpace X).coinduced p := by
    -- Step 3.1: Compare open sets on both sides to establish equality of topologies.
    ext s
    constructor
    · -- Step 3.1.1: Use the continuity of `p` to send open sets forward to open preimages.
      intro hs
      -- Step 3.1.2: By definition of `coinduced`, this says `p ⁻¹' s` is open in `X`.
      change IsOpen (p ⁻¹' s)
      exact h.isOpen_preimage (s := s) hs
    · -- Step 3.2.1: Start from an open set in the coinduced topology.
      intro hs
      -- Step 3.2.2: Reinterpret the hypothesis as openness of `p ⁻¹' s` in `X`.
      have hs' : IsOpen (p ⁻¹' s) := by
        simpa using hs
      -- Step 3.2.3: Pull the set back along `f` using its continuity.
      have h_pre := hf_cont.isOpen_preimage (s := p ⁻¹' s) hs'
      -- Step 3.2.4: Identify the pulled-back set with `s` because `p ∘ f = id`.
      have h_preimage : f ⁻¹' (p ⁻¹' s) = s := by
        ext y
        simp [Set.preimage, hf_pointwise]
      -- Step 3.2.5: Rewrite the openness statement via the identified equality.
      simpa [h_preimage] using h_pre
  -- Step 4: Package the surjectivity and topology equality into the `IsQuotientMap` structure.
  exact ⟨h_surj, h_eq_coinduced⟩
