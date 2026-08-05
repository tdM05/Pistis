import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators



/-Informal Statement

Let $V$ be a vector space over an infinite field $F$. Prove that $V$ is not the union of finitely many proper subspaces.
-/

/-Informal Proof

If $V$ is the set-theoretic union of $n$ proper subspaces $W_i$ ( $1 \leq i \leq n$ ), then $|F| \leq n-1$.
Proof. We may suppose no $W_i$ is contained in the union of the other subspaces. Let $u \in W_i, \quad u \notin \bigcup_{j \neq i} W_j$ and $v \notin W_i$.
Then $(v+F u) \cap W_i=\varnothing$ and $(v+F u) \cap W_j(j \neq i)$ contains at most one vector since otherwise $W_j$ would contain $u$. Hence
$$
|v+F u|=|F| \leq n-1 .
$$
Corollary: Avoidance lemma for vector spaces.
Let $E$ be a vector space over an infinite field. If a subspace is contained in a finite union of subspaces, it is contained in one of them.
-/

theorem Artin_exercise_3_7_2 {K V : Type*} [Field K] [Infinite K] [AddCommGroup V]
  [Module K V] {ι : Type*} [Fintype ι] (γ : ι → Submodule K V)
  (h : ∀ i : ι, γ i ≠ ⊤) :
  (⋃ (i : ι), (γ i : Set V)) ≠ ⊤ := by
  classical
  -- Step 1: Assume (for contradiction) that finitely many proper submodules cover the space.
  intro hUnion
  -- Step 1.1: Package finite unions via a helper `cover` defined on finsets of indices.
  let cover : Finset ι → Set V := fun s => { v | ∃ i ∈ s, v ∈ γ i }
  have cover_univ_eq : cover (Finset.univ : Finset ι) = ⋃ i : ι, (γ i : Set V) := by
    ext v
    constructor
    · rintro ⟨i, -, hi⟩
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    · intro hv
      rcases Set.mem_iUnion.mp hv with ⟨i, hi⟩
      exact ⟨i, Finset.mem_univ _, hi⟩
  have hcover_univ : cover (Finset.univ : Finset ι) = (Set.univ : Set V) := by
    simpa [cover_univ_eq] using hUnion
  -- Step 1.2: Pick a minimal-cardinality finset whose associated cover is `⊤`.
  let P : ℕ → Prop := fun n => ∃ s : Finset ι, s.card = n ∧ cover s = (Set.univ : Set V)
  have hP : ∃ n, P n := ⟨Finset.univ.card, Finset.univ, rfl, hcover_univ⟩
  obtain ⟨s, hs_card, hs_cover⟩ := Nat.find_spec hP
  have hs_min : ∀ t : Finset ι, cover t = (Set.univ : Set V) → s.card ≤ t.card := by
    intro t ht
    have : P t.card := ⟨t, rfl, ht⟩
    have := Nat.find_min' hP this
    simpa [P, hs_card] using this
  -- Step 1.3: Show that `s` is nonempty (else its cover would be empty, contradicting `⊤`).
  have hs_nonempty : s.Nonempty := by
    by_contra hs_empty
    have hs_empty' : s = (∅ : Finset ι) := by
      classical
      cases s.eq_empty_or_nonempty with
      | inl h => simpa using h
      | inr hsne => exact (hs_empty hsne).elim
    have hcover_empty : cover s = (∅ : Set V) := by
      ext v
      simp [cover, hs_empty']
    have hmem : (0 : V) ∈ cover s := by
      have : (0 : V) ∈ (Set.univ : Set V) := by trivial
      simp [hs_cover]
    simp [hcover_empty] at hmem
  -- Step 2: Produce an index `i₀` whose submodule is not contained in the union of the others.
  have h_exists_index : ∃ i ∈ s, ¬ ((γ i : Set V) ⊆ cover (s.erase i)) := by
    classical
    by_contra hAll
    push_neg at hAll
    obtain ⟨i₀, hi₀⟩ := hs_nonempty
    have hsubset : cover s ⊆ cover (s.erase i₀) := by
      intro v hv
      rcases hv with ⟨j, hj, hvj⟩
      by_cases hj₀ : j = i₀
      · subst hj₀
        exact hAll _ hi₀ hvj
      · refine ⟨j, ?_, hvj⟩
        simp [Finset.mem_erase, hj, hj₀]
    have hsubset' : cover (s.erase i₀) ⊆ cover s := by
      intro v hv
      rcases hv with ⟨j, hj, hvj⟩
      rcases Finset.mem_erase.mp hj with ⟨_, hj_in⟩
      exact ⟨j, hj_in, hvj⟩
    have hcover_eq : cover (s.erase i₀) = cover s :=
      Set.Subset.antisymm hsubset' hsubset
    have hcover_top : cover (s.erase i₀) = (Set.univ : Set V) := by
      simpa [hcover_eq] using hs_cover
    have hle := hs_min (s.erase i₀) hcover_top
    have hlt : (s.erase i₀).card < s.card := Finset.card_erase_lt_of_mem hi₀
    exact (lt_irrefl _ ((lt_of_le_of_lt hle hlt)))
  obtain ⟨i₀, hi₀, hi₀_subset⟩ := h_exists_index
  -- Step 2.1: Choose `u ∈ γ i₀` not lying in any other `γ j` with `j ∈ s \ {i₀}`.
  let rest := s.erase i₀
  obtain ⟨u, hu_mem, hu_not⟩ := Set.not_subset.mp hi₀_subset
  -- Step 2.2: Prove that `rest` is nonempty (otherwise `γ i₀` would be `⊤`).
  have hrest_nonempty : rest.Nonempty := by
    by_contra hEmpty
    have hrest_empty : rest = (∅ : Finset ι) := by
      classical
      cases rest.eq_empty_or_nonempty with
      | inl h => simpa using h
      | inr hne => exact (hEmpty hne).elim
    have hUnique : ∀ j ∈ s, j = i₀ := by
      intro j hj
      by_contra hneq
      have : j ∈ rest := by simp [rest, Finset.mem_erase, hj, hneq]
      simp [hrest_empty] at this
    have hs_singleton : s = {i₀} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨hi₀, hUnique⟩
    have hcover_single : cover s = (γ i₀ : Set V) := by
      ext v
      constructor <;> intro hv
      · rcases hv with ⟨j, hj, hvj⟩
        have hj' : j = i₀ := by simpa [hs_singleton] using hj
        simpa [hj'] using hvj
      · exact ⟨i₀, by simp [hs_singleton], hv⟩
    have hγ_univ : (γ i₀ : Set V) = (Set.univ : Set V) := by
      simpa [hcover_single] using hs_cover
    have : γ i₀ = ⊤ := by
      ext v
      constructor
      · intro _; trivial
      · intro _
        have : v ∈ (γ i₀ : Set V) := by
          have : v ∈ (Set.univ : Set V) := by trivial
          simp [hγ_univ]
        simpa using this
    exact (h i₀) this
  -- Step 2.3: Deduce `u ≠ 0` because otherwise it would belong to `rest`'s cover.
  have zero_mem_rest : (0 : V) ∈ cover rest := by
    obtain ⟨j, hj⟩ := hrest_nonempty
    exact ⟨j, hj, (γ j).zero_mem⟩
  have hu_ne_zero : u ≠ 0 := by
    intro hzero
    exact hu_not (by simpa [hzero] using zero_mem_rest)
  -- Step 2.4: Choose `v ∉ γ i₀` since each `γ i` is proper.
  obtain ⟨v, hv_not_mem⟩ : ∃ v : V, v ∉ γ i₀ := by
    classical
    by_contra! hforall
    have : (γ i₀) = ⊤ := by
      ext x
      constructor
      · intro hx; trivial
      · intro _; exact hforall x
    exact (h i₀) this
  -- Step 3: For each remaining submodule, the fiber `{a | v + a • u ∈ γ j}` has ≤ 1 element.
  have hu_not_mem : ∀ {j}, j ∈ rest → u ∉ γ j := by
    intro j hj huj
    exact hu_not ⟨j, hj, huj⟩
  have h_unique : ∀ {j} (hj : j ∈ rest) {a₁ a₂ : K},
      v + a₁ • u ∈ γ j → v + a₂ • u ∈ γ j → a₁ = a₂ := by
    intro j hj a₁ a₂ h₁ h₂
    by_contra hneq
    have hcalc : (v + a₁ • u) - (v + a₂ • u) = a₁ • u - a₂ • u := by
      simp
    have hsmul : (a₁ - a₂) • u ∈ γ j := by
      simpa [hcalc, sub_smul] using (γ j).sub_mem h₁ h₂
    have hscalar : (a₁ - a₂) ≠ 0 := sub_ne_zero.mpr hneq
    have : u ∈ γ j := by
      simpa [smul_smul, hscalar] using (γ j).smul_mem ((a₁ - a₂)⁻¹) hsmul
    exact hu_not_mem hj this
  -- Step 3.1: Collect all ``bad'' scalars as a finite subset of `K`.
  let badSet : Set K := {a : K | ∃ j ∈ rest, v + a • u ∈ γ j}
  have hsubs_singleton : ∀ {j}, j ∈ rest →
      ({a : K | v + a • u ∈ γ j}).Subsingleton := by
    intro j hj
    refine fun {a₁} ha₁ {a₂} ha₂ => ?_
    exact h_unique hj ha₁ ha₂
  have hbad_finite : badSet.Finite := by
    classical
    have hUnion_finite :
        (⋃ j : {j // j ∈ rest}, {a : K | v + a • u ∈ γ j.1}).Finite := by
      refine Set.finite_iUnion ?_
      intro j
      exact (hsubs_singleton j.property).finite
    have hUnion_eq :
        (⋃ j : {j // j ∈ rest}, {a : K | v + a • u ∈ γ j.1}) = badSet := by
      ext a
      constructor
      · intro ha
        rcases Set.mem_iUnion.mp ha with ⟨j, hj⟩
        exact ⟨j.1, j.2, hj⟩
      · intro ha
        rcases ha with ⟨j, hj, hjmem⟩
        exact Set.mem_iUnion.mpr ⟨⟨j, hj⟩, hjmem⟩
    simpa [hUnion_eq] using hUnion_finite
  -- Step 3.2: Use infinitude of `K` to pick a scalar outside this finite obstruction set.
  have huniv_inf : (Set.univ : Set K).Infinite := Set.infinite_univ
  obtain ⟨a, -, ha_not_mem⟩ :=
    Set.Infinite.exists_notMem_finite (s := (Set.univ : Set K)) (t := badSet)
      huniv_inf hbad_finite
  have havoid : ∀ {j}, j ∈ rest → v + a • u ∉ γ j := by
    intro j hj hjmem
    exact ha_not_mem ⟨j, hj, hjmem⟩
  -- Step 4: Show that the chosen element is outside every submodule, contradicting coverage.
  have h_not_i₀ : v + a • u ∉ γ i₀ := by
    intro hmem
    have : v ∈ γ i₀ := by
      have ha_smul : a • u ∈ γ i₀ := (γ i₀).smul_mem a hu_mem
      have := (γ i₀).sub_mem hmem ha_smul
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    exact hv_not_mem this
  have h_not_cover : v + a • u ∉ cover s := by
    intro hmem
    rcases hmem with ⟨j, hj, hjmem⟩
    by_cases hj₀ : j = i₀
    · subst hj₀
      exact h_not_i₀ hjmem
    · have hj_rest : j ∈ rest := by
        simp [rest, Finset.mem_erase, hj, hj₀]
      exact havoid hj_rest hjmem
  have : v + a • u ∈ cover s := by
    have : v + a • u ∈ (Set.univ : Set V) := by trivial
    simp [hs_cover]
  exact h_not_cover this
