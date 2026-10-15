import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Let $X$ be a compact Hausdorff space that is the union of the closed subspaces $X_1$ and $X_2$. If $X_1$ and $X_2$ are metrizable, show that $X$ is metrizable.
-/

/-Informal Proof

Both $X_1$ and $X_2$ are compact, Hausdorff and metrizable, so by exercise 3 they are second countable, i.e. there are countable bases $\left\{U_{i, n} \subset X_i \mid n \in \mathbb{N}\right\}$ for $i \in\{1,2\}$. By the same exercise it is enough to show that $X$ is second countable. If $X_1 \cap X_2=\emptyset$ both $X_1$ and $X_2$ are open and the union $\left\{U_{i, n} \mid i \in\{1,2\} ; n \in \mathbb{N}\right\}$ of their countable bases form a countable base for $X$.

Suppose now $X_1 \cap X_2 \neq \emptyset$. Let $x \in X$ and $U \subset X$ be an open neighborhood of $x$. If $x \in X_i-X_j=X-$ $X_j$ then $U \cap X_i$ is open in $X_i$ and there is a basis neighborhood $U_{i, n}$ of $x$ such that $x \in U_{i, n} \cap X-X_j$ is an open neighborhood of $x$ in the open subset $X-X_j$, so $U_{i, n} \cap X-X_j$ is also open in $X$.
Suppose now that $x \in X_1 \cap X_2$. We have that $U \cap X_i$ is open in $X_i$ so there is a basis neighborhood $U_{i, n_i}$ contained in $U \cap X_i$. By definition of sub-space topology there is some open subset $V_{i, n_i} \subset X$ such that $U_{i, n_i}=$ $X_i \cap V_{i, n_i}$. Then
$$
x \in V_{1, n_1} \cap V_{2, n_2}=\left(V_{1, n_1} \cap V_{2, n_2} \cap X_1\right) \cup\left(V_{1, n_1} \cap V_{2, n_2} \cap X_2\right)=\left(U_{1, n_1} \cap V_{2, n_2}\right) \cup\left(V_{1, n_1} \cap U_{2, n_2}\right) \subset U
$$
Therefore the open subsets $U_{i, n} \cap X-X_j$ and $V_{1, n_1} \cap V_{2, n_2}$ form a countable base for $X$.
-/

theorem Munkres_exercise_34_9
  (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
  (X1 X2 : Set X) (hX1 : IsClosed X1) (hX2 : IsClosed X2)
  (hX : X1 ∪ X2 = univ) (hX1m : MetrizableSpace X1)
  (hX2m : MetrizableSpace X2) : MetrizableSpace X := by
  classical
  -- Step 1: upgrade the closed subspaces `X1` and `X2` to compact second-countable spaces.
  have hX1compact : IsCompact X1 := hX1.isCompact
  have hX2compact : IsCompact X2 := hX2.isCompact
  have _ : CompactSpace X1 := (isCompact_iff_compactSpace).1 hX1compact
  have _ : CompactSpace X2 := (isCompact_iff_compactSpace).1 hX2compact
  -- Step 2: record the canonical countable bases on `X1` and `X2`.
  let B1 := TopologicalSpace.countableBasis X1
  let B2 := TopologicalSpace.countableBasis X2
  have hB1basis : IsTopologicalBasis B1 := TopologicalSpace.isBasis_countableBasis X1
  have hB2basis : IsTopologicalBasis B2 := TopologicalSpace.isBasis_countableBasis X2
  have hB1count : B1.Countable := TopologicalSpace.countable_countableBasis X1
  have hB2count : B2.Countable := TopologicalSpace.countable_countableBasis X2
  -- Step 3: package each basis element together with the data of an ambient open set in `X`.
  let S1 := { s : Set X1 // s ∈ B1 }
  let S2 := { s : Set X2 // s ∈ B2 }
  have hS1count : Countable S1 := hB1count.to_subtype
  have hS2count : Countable S2 := hB2count.to_subtype
  have hLift1 :
      ∀ s : S1, ∃ V : Set X, IsOpen V ∧ Subtype.val ⁻¹' V = (s : Set X1) := by
        -- Step 3.1: every basis element is open in the subspace, hence comes from an open subset of `X`.
        intro s
        have hsopen : IsOpen (s : Set X1) :=
          TopologicalSpace.isOpen_of_mem_countableBasis (α := X1) s.property
        simpa [S1] using (isOpen_induced_iff.mp hsopen)
  have hLift2 :
      ∀ s : S2, ∃ V : Set X, IsOpen V ∧ Subtype.val ⁻¹' V = (s : Set X2) := by
        -- Step 3.2: same construction for the second closed subspace.
        intro s
        have hsopen : IsOpen (s : Set X2) :=
          TopologicalSpace.isOpen_of_mem_countableBasis (α := X2) s.property
        simpa [S2] using (isOpen_induced_iff.mp hsopen)
  -- Step 4: choose concrete ambient open supersets for every basis element.
  choose lift1 hLift1open hLift1preimage using hLift1
  choose lift2 hLift2open hLift2preimage using hLift2
  -- Step 5: build the candidate global basis consisting of three countable families.
  let ℬ₁ : Set (Set X) := Set.range fun s : S1 => lift1 s ∩ X2ᶜ
  let ℬ₂ : Set (Set X) := Set.range fun s : S2 => lift2 s ∩ X1ᶜ
  let ℬ₁₂ : Set (Set X) := Set.range fun p : S1 × S2 => lift1 p.1 ∩ lift2 p.2
  let ℬ : Set (Set X) := ℬ₁ ∪ ℬ₂ ∪ ℬ₁₂
  -- Step 6: keep track of the obvious open sets that will appear repeatedly.
  have hOpenX1c : IsOpen X1ᶜ := hX1.isOpen_compl
  have hOpenX2c : IsOpen X2ᶜ := hX2.isOpen_compl
  -- Step 7: note that every point outside `X2` (resp. `X1`) actually lies in `X1` (resp. `X2`)
  -- thanks to the covering hypothesis.
  have hSubsetX1 : X2ᶜ ⊆ X1 := by
    intro x hx
    have hxUnion : x ∈ X1 ∪ X2 := by simp [hX]
    rcases hxUnion with hxUnion | hxUnion
    · exact hxUnion
    · exact (hx hxUnion).elim
  have hSubsetX2 : X1ᶜ ⊆ X2 := by
    intro x hx
    have hxUnion : x ∈ X1 ∪ X2 := by simp [hX]
    rcases hxUnion with hxUnion | hxUnion
    · exact (hx hxUnion).elim
    · exact hxUnion
  -- Step 8: check that all sets in ℬ are open.
  have hOpenℬ : ∀ U ∈ ℬ, IsOpen U := by
    intro U hU
    rcases hU with hU | hU
    · rcases hU with hU | hU
      · rcases hU with ⟨s, rfl⟩
        exact (hLift1open s).inter hOpenX2c
      · rcases hU with ⟨s, rfl⟩
        exact (hLift2open s).inter hOpenX1c
    · rcases hU with ⟨p, rfl⟩
      exact (hLift1open p.1).inter (hLift2open p.2)
  -- Step 9: prove the local basis property demanded by `isTopologicalBasis_of_isOpen_of_nhds`.
  have hBasisℬ :
      IsTopologicalBasis ℬ := by
        refine
          isTopologicalBasis_of_isOpen_of_nhds hOpenℬ ?_
        -- Step 9.1: fix an arbitrary point and an open neighbourhood.
        intro x U hxU hUopen
        have hxUnion : x ∈ X1 ∪ X2 := by simp [hX]
        -- Step 9.2: split into the three mutually exclusive cases.
        by_cases hx1 : x ∈ X1
        · by_cases hx2 : x ∈ X2
          -- Step 9.2.1: x belongs to both closed subspaces.
          ·
            -- Step 9.2.1.1: build basic neighbourhoods inside X1 and X2.
            set x1 : X1 := ⟨x, hx1⟩
            set x2 : X2 := ⟨x, hx2⟩
            have hUx1 :
                IsOpen ((Subtype.val : X1 → X) ⁻¹' U) :=
              (continuous_subtype_val :
                  Continuous fun p : X1 => (p : X)).isOpen_preimage
                (s := U) hUopen
            have hUx2 :
                IsOpen ((Subtype.val : X2 → X) ⁻¹' U) :=
              (continuous_subtype_val :
                  Continuous fun p : X2 => (p : X)).isOpen_preimage
                (s := U) hUopen
            have hxUx1 : x1 ∈ (Subtype.val : X1 → X) ⁻¹' U := by
              simpa using hxU
            have hxUx2 : x2 ∈ (Subtype.val : X2 → X) ⁻¹' U := by
              simpa using hxU
            obtain ⟨s, hsB1, hxs, hsSubset⟩ :=
              hB1basis.exists_subset_of_mem_open hxUx1 hUx1
            obtain ⟨t, htB2, hxt, htSubset⟩ :=
              hB2basis.exists_subset_of_mem_open hxUx2 hUx2
            -- Step 9.2.1.2: pass back to open subsets of X and assemble an element of ℬ₁₂.
            refine ⟨lift1 ⟨s, hsB1⟩ ∩ lift2 ⟨t, htB2⟩,
              Or.inr ⟨⟨⟨s, hsB1⟩, ⟨t, htB2⟩⟩, rfl⟩, ?_, ?_⟩
            · -- Step 9.2.1.3: x lies in the constructed basic open.
              have hxs' :
                  (x : X) ∈ lift1 ⟨s, hsB1⟩ := by
                have :
                    (x1 : X1) ∈ (Subtype.val : X1 → X) ⁻¹' lift1 ⟨s, hsB1⟩ := by
                  simpa [hLift1preimage ⟨s, hsB1⟩] using hxs
                simpa using this
              have hxt' :
                  (x : X) ∈ lift2 ⟨t, htB2⟩ := by
                have :
                    (x2 : X2) ∈ (Subtype.val : X2 → X) ⁻¹' lift2 ⟨t, htB2⟩ := by
                  simpa [hLift2preimage ⟨t, htB2⟩] using hxt
                simpa using this
              exact ⟨hxs', hxt'⟩
            · -- Step 9.2.1.4: any point in this basic open still lies inside the target open set.
              intro z hz
              have hzUnion : z ∈ X1 ∪ X2 := by simp [hX]
              rcases hzUnion with hzUnion | hzUnion
              ·
                have hzX1 : z ∈ X1 := hzUnion
                have hzmem :
                    (⟨z, hzX1⟩ : X1) ∈ s := by
                  have hzpre :
                      (⟨z, hzX1⟩ : X1) ∈
                        (Subtype.val : X1 → X) ⁻¹' lift1 ⟨s, hsB1⟩ := by
                    simpa using hz.1
                  simpa [hLift1preimage ⟨s, hsB1⟩] using hzpre
                have := hsSubset hzmem
                simpa using this
              ·
                have hzX2 : z ∈ X2 := hzUnion
                have hzmem :
                    (⟨z, hzX2⟩ : X2) ∈ t := by
                  have hzpre :
                      (⟨z, hzX2⟩ : X2) ∈
                        (Subtype.val : X2 → X) ⁻¹' lift2 ⟨t, htB2⟩ := by
                    simpa using hz.2
                  simpa [hLift2preimage ⟨t, htB2⟩] using hzpre
                have := htSubset hzmem
                simpa using this
          -- Step 9.2.2: x belongs to X1 but not to X2.
          ·
            set x1 : X1 := ⟨x, hx1⟩
            have hUx1 :
                IsOpen ((Subtype.val : X1 → X) ⁻¹' U) :=
              (continuous_subtype_val :
                  Continuous fun p : X1 => (p : X)).isOpen_preimage
                (s := U) hUopen
            have hxUx1 : x1 ∈ (Subtype.val : X1 → X) ⁻¹' U := by
              simpa using hxU
            obtain ⟨s, hsB1, hxs, hsSubset⟩ :=
              hB1basis.exists_subset_of_mem_open hxUx1 hUx1
            refine ⟨lift1 ⟨s, hsB1⟩ ∩ X2ᶜ,
              Or.inl <| Or.inl ⟨⟨s, hsB1⟩, rfl⟩, ?_, ?_⟩
            ·
              have hxs' :
                  (x : X) ∈ lift1 ⟨s, hsB1⟩ := by
                have :
                    (x1 : X1) ∈ (Subtype.val : X1 → X) ⁻¹' lift1 ⟨s, hsB1⟩ := by
                  simpa [hLift1preimage ⟨s, hsB1⟩] using hxs
                simpa using this
              exact ⟨hxs', by simpa using hx2⟩
            ·
              intro z hz
              have hzX1 : z ∈ X1 := hSubsetX1 hz.2
              have hzmem :
                  (⟨z, hzX1⟩ : X1) ∈ s := by
                have hzpre :
                    (⟨z, hzX1⟩ : X1) ∈
                      (Subtype.val : X1 → X) ⁻¹' lift1 ⟨s, hsB1⟩ := by
                  simpa using hz.1
                simpa [hLift1preimage ⟨s, hsB1⟩] using hzpre
              have := hsSubset hzmem
              simpa using this
        -- Step 9.2.3: x does not belong to X1, so it must lie in X2 by the covering hypothesis.
        ·
          have hx2 : x ∈ X2 := by
            rcases hxUnion with hxUnion | hxUnion
            · exact (hx1 hxUnion).elim
            · exact hxUnion
          set x2 : X2 := ⟨x, hx2⟩
          have hUx2 :
              IsOpen ((Subtype.val : X2 → X) ⁻¹' U) :=
            (continuous_subtype_val :
                Continuous fun p : X2 => (p : X)).isOpen_preimage
              (s := U) hUopen
          have hxUx2 : x2 ∈ (Subtype.val : X2 → X) ⁻¹' U := by
            simpa using hxU
          obtain ⟨s, hsB2, hxs, hsSubset⟩ :=
            hB2basis.exists_subset_of_mem_open hxUx2 hUx2
          refine ⟨lift2 ⟨s, hsB2⟩ ∩ X1ᶜ,
            Or.inl <| Or.inr ⟨⟨s, hsB2⟩, rfl⟩, ?_, ?_⟩
          ·
            have hxs' :
                (x : X) ∈ lift2 ⟨s, hsB2⟩ := by
              have :
                  (x2 : X2) ∈ (Subtype.val : X2 → X) ⁻¹' lift2 ⟨s, hsB2⟩ := by
                simpa [hLift2preimage ⟨s, hsB2⟩] using hxs
              simpa using this
            exact ⟨hxs', by simpa using hx1⟩
          ·
            intro z hz
            have hzX2 : z ∈ X2 := hSubsetX2 hz.2
            have hzmem :
                (⟨z, hzX2⟩ : X2) ∈ s := by
              have hzpre :
                  (⟨z, hzX2⟩ : X2) ∈
                    (Subtype.val : X2 → X) ⁻¹' lift2 ⟨s, hsB2⟩ := by
                simpa using hz.1
              simpa [hLift2preimage ⟨s, hsB2⟩] using hzpre
            have := hsSubset hzmem
            simpa using this
  -- Step 10: register that ℬ is countable.
  have hℬcount : ℬ.Countable := by
    have hℬ₁count : ℬ₁.Countable :=
      (countable_range fun s : S1 => lift1 s ∩ X2ᶜ)
    have hℬ₂count : ℬ₂.Countable :=
      (countable_range fun s : S2 => lift2 s ∩ X1ᶜ)
    have hℬ₁₂count : ℬ₁₂.Countable :=
      (countable_range fun p : S1 × S2 => lift1 p.1 ∩ lift2 p.2)
    exact (hℬ₁count.union hℬ₂count).union hℬ₁₂count
  -- Step 11: obtain a second-countable topology on `X` from the constructed basis.
  have hSC : SecondCountableTopology X := hBasisℬ.secondCountableTopology hℬcount
  -- Step 12: conclude metrizability via Urysohn's metrization theorem for compact Hausdorff spaces.
  exact TopologicalSpace.metrizableSpace_of_t3_secondCountable X
