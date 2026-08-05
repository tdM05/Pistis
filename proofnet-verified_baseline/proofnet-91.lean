import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

Let $V$ be a vector space over an infinite field $F$. Show that $V$ cannot be the set-theoretic union of a finite number of proper subspaces of $V$.
-/

/-Informal Proof

Assume that $V$ can be written as the set-theoretic union of $n$ proper subspaces $U_1, U_2, \ldots, U_n$. Without loss of generality, we may assume that no $U_i$ is contained in the union of other subspaces.

Let $u \in U_i$ but $u \notin \bigcup_{j \neq i} U_j$ and $v \notin U_i$. Then, we have $(v + Fu) \cap U_i = \varnothing$, and $(v + Fu) \cap U_j$ for $j \neq i$ contains at most one vector, since otherwise $U_j$ would contain $u$.

Therefore, we have $|v + Fu| \leq |F| \leq n-1$. However, since $n$ is a finite natural number, this contradicts the fact that the field $F$ is finite.

Thus, our assumption that $V$ can be written as the set-theoretic union of proper subspaces is wrong, and the claim is proven.
-/

theorem Herstein_exercise_5_2_20 {F V ι: Type*} [Infinite F] [Field F]
  [AddCommGroup V] [Module F V] [Finite ι] {u : ι → Submodule F V}
  (hu : ∀ i : ι, u i ≠ ⊤) :
  (⋃ i : ι, (u i : Set V)) ≠ ⊤ := by
  classical
  -- Step 1: Endow the finite index type with explicit finite combinatorial structure.
  haveI := Fintype.ofFinite ι
  -- Step 2: Build an inductive helper guaranteeing a vector outside any prescribed finite family.
  have exists_not_mem :
      ∀ s : Finset ι,
        (∀ i ∈ s, u i ≠ ⊤) →
          ∃ v : V, ∀ i ∈ s, v ∉ (u i : Set V) := by
    classical
    -- Step 2.1: Tackle the empty family where the goal is vacuous.
    refine Finset.induction ?base ?step
    · intro _
      -- Step 2.1.1: Use the zero vector because no avoidance conditions exist.
      refine ⟨0, ?_⟩
      intro i hi
      -- Step 2.1.2: Membership in the empty index set is impossible.
      cases hi
    · intro a s ha ih hs
      -- Step 2.2.1: Isolate the hypotheses for the tail `s` and the new head `a`.
      have hs' : ∀ i ∈ s, u i ≠ ⊤ := by
        intro i hi
        exact hs i (Finset.mem_insert_of_mem hi)
      have ha' : u a ≠ ⊤ := by
        have : a ∈ insert a s := by
          simp
        exact hs a this
      -- Step 2.2.2: Obtain a witness `w` already avoiding every submodule in `s`.
      obtain ⟨w, hw⟩ := ih hs'
      -- Step 2.2.3: Distinguish whether `w` also escapes the new submodule `u a`.
      by_cases hwa : w ∈ (u a : Set V)
      · -- Step 2.2.3.1: Deal with the difficult case where `w` lies inside `u a`.
        -- Step 2.2.3.1.1: Produce a direction `y` definitely outside `u a`.
        have hy_exists : ∃ y : V, y ∉ (u a : Set V) := by
          classical
          by_contra h
          have hall : ∀ y : V, y ∈ (u a : Set V) := by
            intro y
            have hyneg : ¬ y ∉ (u a : Set V) := not_exists.mp h y
            exact not_not.mp (by simpa using hyneg)
          have htop : (⊤ : Submodule F V) ≤ u a := by
            intro x _
            exact hall x
          have : u a = ⊤ := le_antisymm le_top htop
          exact ha' this
        obtain ⟨y, hy⟩ := hy_exists
        -- Step 2.2.3.1.2: Collect the offending scalars into a finite set `bad`.
        classical
        let indices : Finset ι := insert a s
        let badList :
            List F :=
          indices.toList.filterMap fun i =>
            if hmem : ∃ t : F, w + t • y ∈ u i then
              some (Classical.choose hmem)
            else
              none
        let bad : Finset F := badList.toFinset
        -- Step 2.2.3.1.4: Exploit the infinitude of the field to find a scalar outside `bad`.
        obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset (s := bad)
        have ht' : t ∉ bad := ht
        -- Step 2.2.3.1.5: Record the uniqueness of scalars mapping the affine line back into any submodule.
        have unique_scalar :
            ∀ {i : ι} {t₁ t₂ : F},
              y ∉ (u i : Set V) →
              w + t₁ • y ∈ u i →
              w + t₂ • y ∈ u i →
              t₁ = t₂ := by
          intro i t₁ t₂ hyi ht₁ ht₂
          have hdiff := (u i).sub_mem ht₁ ht₂
          have h1 :
              (w + t₁ • y) - (w + t₂ • y)
                  = t₁ • y - t₂ • y := by
            simp [sub_add_eq_sub_sub]
          have h2 :
              t₁ • y - t₂ • y = (t₁ - t₂) • y := by
            simpa using (sub_smul t₁ t₂ y).symm
          have hsmul :
              (t₁ - t₂) • y ∈ u i := by
            simpa [h1, h2] using hdiff
          -- Step 2.2.3.1.5.2: A non-zero coefficient would force `y` back into `u i`, contradicting `hyi`.
          by_contra hneq
          have hcoeff : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr hneq
          have hyi' : y ∈ u i := by
            have : ((t₁ - t₂)⁻¹) • ((t₁ - t₂) • y) ∈ u i :=
              (u i).smul_mem ((t₁ - t₂)⁻¹) hsmul
            simpa [smul_smul, hcoeff, inv_mul_cancel, one_smul] using this
          exact hyi hyi'
        -- Step 2.2.3.1.6: Move along the affine line determined by `y` using the safe scalar `t`.
        let z : V := w + t • y
        refine ⟨z, ?_⟩
        intro i hi
        have hi' := Finset.mem_insert.mp hi
        cases hi' with
        | inl hia =>
            -- Step 2.2.3.1.7: Show that the new vector escapes `u i` (which equals `u a`).
            intro hz
            have hmem : ∃ t₀ : F, w + t₀ • y ∈ u i := ⟨t, by simpa [z] using hz⟩
            have hyi : y ∉ (u i : Set V) := by
              simpa [hia] using hy
            have hchoose :
                Classical.choose hmem = t := by
              apply unique_scalar
              · exact hyi
              · exact Classical.choose_spec hmem
              · simpa [z] using hz
            have : t ∈ bad := by
              have hiList :
                  i ∈ indices.toList := by
                have : i ∈ indices := by
                  simp [indices, hia]
                exact (Finset.mem_toList).2 this
              have hmemList :
                  t ∈ badList := by
                refine List.mem_filterMap.2 ?_
                refine ⟨i, hiList, ?_⟩
                simp [hmem, hchoose]
              have : t ∈ badList.toFinset := List.mem_toFinset.mpr hmemList
              simpa [bad] using this
            exact ht' this
        | inr his =>
            -- Step 2.2.3.1.8: Show that the new vector also escapes every submodule indexed by `s`.
            intro hz
            have hmem : ∃ t₀ : F, w + t₀ • y ∈ u i := ⟨t, by simpa [z] using hz⟩
            have hyi : y ∉ (u i : Set V) := by
              intro hyi
              have hsmul : t • y ∈ u i := (u i).smul_mem t hyi
              have hz' : w + t • y ∈ u i := by simpa [z] using hz
              have hw_mem : w ∈ u i := by
                have := (u i).sub_mem hz' hsmul
                simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
              exact (hw i his) hw_mem
            have hchoose :
                Classical.choose hmem = t := by
              apply unique_scalar
              · exact hyi
              · exact Classical.choose_spec hmem
              · simpa [z] using hz
            have : t ∈ bad := by
              have hiList :
                  i ∈ indices.toList := by
                have : i ∈ indices := by
                  simpa [indices] using Finset.mem_insert.mpr (Or.inr his)
                exact (Finset.mem_toList).2 this
              have hmemList :
                  t ∈ badList := by
                refine List.mem_filterMap.2 ?_
                refine ⟨i, hiList, ?_⟩
                simp [hmem, hchoose]
              have : t ∈ badList.toFinset := List.mem_toFinset.mpr hmemList
              simpa [bad] using this
            exact ht' this
      · -- Step 2.2.3.2: Keep `w` when it already avoids `u a`.
        refine ⟨w, ?_⟩
        intro i hi
        have hi' := Finset.mem_insert.mp hi
        cases hi' with
        | inl hia =>
            subst hia
            exact hwa
        | inr his =>
            exact hw i his
  -- Step 3: Apply the helper lemma to the full finite index set.
  have hs0 : ∀ i ∈ (Finset.univ : Finset ι), u i ≠ ⊤ := by
    intro i _
    simpa using hu i
  obtain ⟨v, hv⟩ := exists_not_mem (Finset.univ : Finset ι) hs0
  -- Step 4: Exhibit an explicit element outside the finite union.
  have hv_union : v ∉ ⋃ i : ι, (u i : Set V) := by
    intro hmem
    classical
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hmem
    exact (hv i (Finset.mem_univ i)) hi
  -- Step 5: Conclude that the union cannot coincide with the entire space.
  intro htop
  have hv_top : v ∈ (⊤ : Set V) := by trivial
  have hv_union_mem : v ∈ ⋃ i : ι, (u i : Set V) := by
    simp [htop]
  exact hv_union hv_union_mem
