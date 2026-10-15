import Mathlib

open Filter Set TopologicalSpace Topology



/-Informal Statement

If $A \subset X$, a retraction of $X$ onto $A$ is a continuous map $r: X \rightarrow A$ such that $r(a)=a$ for each $a \in A$. Show that a retraction is a quotient map.
-/

/-Informal Proof

The inclusion map $i: A \rightarrow X$ is continuous and $r \circ i=1_A$ is the identity. Thus $r$ is a quotient map by (a).
-/

theorem Munkres_exercise_22_2b {X : Type*} [TopologicalSpace X]
  {A : Set X} (r : X → A) (hr : Continuous r) (h : ∀ x : A, r x = x) :
  IsQuotientMap r := by
  classical
  -- Step 1: Invoke the characterization of quotient maps via surjectivity and open-set equivalence.
  refine (Topology.isQuotientMap_iff (f := r)).mpr ?_
  -- Step 1.1: Prove that `r` is surjective by using that it fixes every point of `A`.
  refine ⟨?_, ?_⟩
  -- Step 1.1.1: For each `y : A`, take `y` itself (viewed in `X`) as a preimage.
  refine fun y => ⟨(y : X), ?_⟩
  -- Step 1.1.1.1: Apply the retraction hypothesis `h` to conclude `r y = y`.
  simpa using h y
  -- Step 1.2: Show that a subset of `A` is open iff its preimage under `r` is open in `X`.
  intro s
  constructor
  · -- Step 1.2.1: Start from an open set `s` in `A` and exhibit an ambient open `U ⊆ X`.
    intro hs
    -- Step 1.2.1.1: Extract an open set `U` in `X` whose pullback along the inclusion equals `s`.
    rcases (show ∃ U : Set X, IsOpen U ∧ (Subtype.val : A → X) ⁻¹' U = s from by
        simpa using hs) with ⟨U, hU_open, hU_eq⟩
    -- Step 1.2.1.3: Record the continuity of the composite `x ↦ (r x : A) ↦ (r x : X)`.
    have h_toX : Continuous fun x : X => ((r x : A) : X) :=
      continuous_subtype_val.comp hr
    -- Step 1.2.1.4: Identify the relevant preimage set by comparing memberships pointwise.
    have h_preimage_eq :
        r ⁻¹' s = (fun x : X => ((r x : A) : X)) ⁻¹' U := by
      -- Step 1.2.1.4.1: Use set extensionality to compare both sides elementwise.
      ext x
      constructor <;> intro hx
      · -- Step 1.2.1.4.1.1: Rewrite membership in `s` via the description supplied by `hU_eq`.
        have hx' : r x ∈ Subtype.val ⁻¹' U := by
          simpa [hU_eq] using hx
        -- Step 1.2.1.4.1.2: Unfold the definition of the preimage along the inclusion.
        simpa [Set.mem_preimage] using hx'
      · -- Step 1.2.1.4.1.3: Start with the preimage condition in `X` and return to `s`.
        have hx' : ((r x : A) : X) ∈ U := by
          simpa using hx
        have hx'' : r x ∈ Subtype.val ⁻¹' U := by
          simpa [Set.mem_preimage] using hx'
        -- Step 1.2.1.4.1.4: Translate back to membership in `s`.
        simpa [hU_eq] using hx''
    -- Step 1.2.1.5: Pull back the open set `U` along the continuous map `x ↦ (r x : X)`.
    have h_preimage_open :
        IsOpen (r ⁻¹' s) := by
      -- Step 1.2.1.5.1: Apply continuity and then substitute the pointwise equality.
      simpa [h_preimage_eq] using hU_open.preimage h_toX
    -- Step 1.2.1.6: Conclude that `r ⁻¹' s` is open in `X`.
    exact h_preimage_open
  · -- Step 1.2.2: Assume the preimage `r ⁻¹' s` is open in `X` and deduce that `s` is open in `A`.
    intro hs
    -- Step 1.2.2.1: Name the open subset of `X` obtained as the preimage.
    let V : Set X := r ⁻¹' s
    have hV_open : IsOpen V := hs
    -- Step 1.2.2.2: Show that the pullback of `V` along the inclusion coincides with `s`.
    have h_pullback :
        (Subtype.val : A → X) ⁻¹' V = s := by
      -- Step 1.2.2.2.1: Compare membership elementwise.
      ext a
      constructor <;> intro ha
      · -- Step 1.2.2.2.1.1: Expand `ha` into the statement `r a ∈ s`.
        have ha' : r a ∈ s := by
          simpa [V, Set.mem_preimage] using ha
        -- Step 1.2.2.2.1.2: Use `h` to replace `r a` with `a`.
        simpa [h a] using ha'
      · -- Step 1.2.2.2.1.3: Start from `a ∈ s` and view it through the preimage description.
        have ha' : r a ∈ s := by
          simpa [h a] using ha
        -- Step 1.2.2.2.1.4: Translate back to the preimage along the inclusion.
        simpa [V, Set.mem_preimage] using ha'
    -- Step 1.2.2.3: Translate the data into the induced-topology characterization of openness.
    have : ∃ U : Set X, IsOpen U ∧ (Subtype.val : A → X) ⁻¹' U = s :=
      ⟨V, hV_open, h_pullback⟩
    -- Step 1.2.2.4: Return to the ambient notation for `IsOpen s`.
    simpa using this
