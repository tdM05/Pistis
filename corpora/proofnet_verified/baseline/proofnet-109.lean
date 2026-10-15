import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

def lower_limit_topology (X : Type) [Preorder X] :=
  generateFrom {S : Set X | ∃ a b, a < b ∧ S = Ico a b}

def Rl := lower_limit_topology ℝ

def K : Set ℝ := {r | ∃ n : ℕ, r = 1 / (n + 1 : ℝ)}

def K_topology := generateFrom
  ({S : Set ℝ | ∃ a b, a < b ∧ S = Ioo a b} ∪ {S : Set ℝ | ∃ a b, a < b ∧ S = Ioo a b \ K})

/-Informal Statement

Show that the lower limit topology $\mathbb{R}_l$ and $K$-topology $\mathbb{R}_K$ are not comparable.
-/

/-Informal Proof

Let $\mathcal{T}_{\ell}$ and $\mathcal{T}_K$ denote the topologies of $\mathbb{R}_{\ell}$ and $\mathbb{R}_K$ respectively. Given the basis element $[0,1)$ for $\mathcal{T}_{\ell}$, there is no basis element for $\mathcal{T}_K$ containing 0 and contained in $[0,1)$, so $\mathcal{T}_{\ell} \not \subset \mathcal{T}_K$. Similarly, given the basis element $(-1,1) \backslash K$ for $\mathcal{T}_K$, there is no basis element for $\mathcal{T}_{\ell}$ containing 0 contained in $(-1,1) \backslash K$, so $\mathcal{T}_K \not \subset \mathcal{T}_{\ell}$.
-/

theorem Munkres_exercise_13_6 :
  ¬ (∀ U, Rl.IsOpen U → K_topology.IsOpen U) ∧ ¬ (∀ U, K_topology.IsOpen U → Rl.IsOpen U) := by
  classical
  -- Step 1: Prove that `[0,1)` is open in the lower-limit topology `Rl`.
  -- Step 1.1: Observe that `[0,1)` is one of the generating sets for `Rl`.
  have h_Rl_open_Ico : Rl.IsOpen (Ico (0 : ℝ) 1) := by
    -- Step 1.1.1: Show that `[0,1)` belongs to the generating family for `lower_limit_topology ℝ`.
    have h_mem_gen :
        Ico (0 : ℝ) 1 ∈ {S : Set ℝ | ∃ a b, a < b ∧ S = Ico a b} := by
      -- Step 1.1.1.1: Witness this membership with `a = 0` and `b = 1`.
      exact ⟨0, 1, by norm_num, rfl⟩
    -- Step 1.1.2: Apply the general lemma turning membership in the generating family into openness.
    simpa [Rl, lower_limit_topology] using
      (TopologicalSpace.isOpen_generateFrom_of_mem h_mem_gen)

  -- Step 2: Show that `[0,1)` is *not* open in the `K`-topology.
  -- Step 2.1: Name the generating family `g` for `K_topology` to make later rewriting convenient.
  let g : Set (Set ℝ) :=
    {S : Set ℝ | ∃ a b, a < b ∧ S = Ioo a b} ∪
      {S : Set ℝ | ∃ a b, a < b ∧ S = Ioo a b \ K}
  have h_Ktop_def : K_topology = TopologicalSpace.generateFrom g := by
    -- Step 2.1.1: This is just a restatement of the definition of `K_topology`.
    rfl

  -- Step 2.2: Establish a key lemma: any open set in `K_topology` containing `0`
  --           must contain an interval of the form `(-ε, 0)`.
  have h_K_open_zero_has_neg_interval :
      ∀ {U : Set ℝ},
        TopologicalSpace.GenerateOpen g U →
        (0 : ℝ) ∈ U →
        ∃ ε > (0 : ℝ), Ioo (-ε) 0 ⊆ U := by
    -- Step 2.2.1: Prove the statement by induction on the `GenerateOpen` derivation.
    intro U hU
    induction hU with
    | basic s hs =>
        -- Step 2.2.1.1: Base case – `U` is one of the generators `s ∈ g`.
        intro h0s
        -- Step 2.2.1.1.1: Unpack the fact that `s` lies in the union defining `g`.
        have hs_union :
            s ∈ {S : Set ℝ | ∃ a b, a < b ∧ S = Ioo a b} ∨
              s ∈ {S : Set ℝ | ∃ a b, a < b ∧ S = Ioo a b \ K} := by
          simpa [g] using hs
        -- Step 2.2.1.1.2: Split into the two concrete generator shapes.
        cases hs_union with
        | inl hIoo =>
            -- Step 2.2.1.1.2.1: Case `s = (a,b)` with `a < b`.
            rcases hIoo with ⟨a, b, hab, rfl⟩
            -- Step 2.2.1.1.2.2: Use `0 ∈ (a,b)` to deduce `a < 0` and `0 < b`.
            rcases h0s with ⟨ha0, h0b⟩
            -- Step 2.2.1.1.2.3: Choose `ε = -a > 0` so that `(-ε,0) = (a,0)`.
            refine ⟨-a, ?_, ?_⟩
            · -- Step 2.2.1.1.2.3.1: Positivity of `ε = -a` follows from `a < 0`.
              exact neg_pos.mpr ha0
            · -- Step 2.2.1.1.2.3.2: Show `(-ε,0) ⊆ (a,b)`.
              intro y hy
              -- Step 2.2.1.1.2.3.2.1: Unpack membership in `(-ε,0) = (a,0)`.
              have hy_left : a < y := by
                -- Here `hy.1 : -(-a) < y`, so rewrite and simplify.
                simpa using hy.1
              have hy_right : y < 0 := hy.2
              -- Step 2.2.1.1.2.3.2.2: Combine with `0 < b` to get `y < b`.
              have hy_lt_b : y < b := lt_trans hy_right h0b
              exact ⟨hy_left, hy_lt_b⟩
        | inr hDiff =>
            -- Step 2.2.1.1.2.4: Case `s = (a,b) \ K` with `a < b`.
            rcases hDiff with ⟨a, b, hab, rfl⟩
            -- Step 2.2.1.1.2.5: `0 ∈ (a,b) \ K` gives `0 ∈ (a,b)` and `0 ∉ K`.
            rcases h0s with ⟨h0Ioo, _h0notK⟩
            rcases h0Ioo with ⟨ha0, h0b⟩
            -- Step 2.2.1.1.2.6: Again choose `ε = -a > 0`.
            refine ⟨-a, ?_, ?_⟩
            · -- Step 2.2.1.1.2.6.1: Positivity of `ε`.
              exact neg_pos.mpr ha0
            · -- Step 2.2.1.1.2.6.2: Show `(-ε,0) ⊆ (a,b) \ K`.
              intro y hy
              -- Step 2.2.1.1.2.6.2.1: First place `y` into `(a,b)`.
              have hy_left : a < y := by
                simpa using hy.1
              have hy_right : y < 0 := hy.2
              have hy_lt_b : y < b := lt_trans hy_right h0b
              -- Step 2.2.1.1.2.6.2.2: Show `y ∉ K` using `y < 0` and positivity of all elements of `K`.
              have hy_notK : y ∉ K := by
                -- Assume `y ∈ K` and derive a contradiction.
                intro hyK
                rcases hyK with ⟨n, hy_eq⟩
                -- Every point of `K` is nonnegative.
                have hy_nonneg : (0 : ℝ) ≤ y := by
                  -- Use `y = 1 / (n + 1)` and `one_div_nonneg`.
                  have h_nat_nonneg : (0 : ℝ) ≤ (n + 1 : ℝ) := by
                    -- `n + 1` is a natural number, hence nonnegative as a real.
                    exact_mod_cast (Nat.zero_le (n + 1))
                  have h_div_nonneg : (0 : ℝ) ≤ 1 / (n + 1 : ℝ) :=
                    (one_div_nonneg.mpr h_nat_nonneg)
                  simpa [hy_eq] using h_div_nonneg
                -- But we also know `y < 0`, so no such `y` can lie in `K`.
                exact (not_le_of_gt hy_right) hy_nonneg
              -- Step 2.2.1.1.2.6.2.3: Collect both facts as membership in `(a,b) \ K`.
              exact ⟨⟨hy_left, hy_lt_b⟩, hy_notK⟩
    | univ =>
        -- Step 2.2.1.2: Base case – `U = univ`.
        intro _h0
        -- Step 2.2.1.2.1: Take a fixed positive `ε`, say `ε = 1`.
        refine ⟨(1 : ℝ), by norm_num, ?_⟩
        -- Step 2.2.1.2.2: Any subset of `univ` is trivially contained in it.
        intro _y _hy
        trivial
    | inter s t hs ht ihs iht =>
        -- Step 2.2.1.3: Inductive step – intersection of two generated opens.
        intro h0st
        -- Step 2.2.1.3.1: Split the fact that `0 ∈ s ∩ t`.
        rcases h0st with ⟨h0s, h0t⟩
        -- Step 2.2.1.3.2: Apply the induction hypotheses to both halves.
        rcases ihs h0s with ⟨ε₁, hε₁_pos, h_sub₁⟩
        rcases iht h0t with ⟨ε₂, hε₂_pos, h_sub₂⟩
        -- Step 2.2.1.3.3: Work with the smaller of the two radii.
        let ε := min ε₁ ε₂
        have hε_pos : (0 : ℝ) < ε := by
          -- `0 < min ε₁ ε₂` since both `ε₁` and `ε₂` are positive.
          exact (lt_min_iff).2 ⟨hε₁_pos, hε₂_pos⟩
        -- Step 2.2.1.3.4: Show that `(-ε,0)` is contained in each of the original intervals.
        have h_sub_to₁ : Ioo (-ε) 0 ⊆ Ioo (-ε₁) 0 := by
          intro y hy
          have hy_right : y < 0 := hy.2
          have hε_le_ε₁ : ε ≤ ε₁ := min_le_left _ _
          have hneg_le : -ε₁ ≤ -ε := neg_le_neg hε_le_ε₁
          have hy_left : -ε₁ < y := lt_of_le_of_lt hneg_le hy.1
          exact ⟨hy_left, hy_right⟩
        have h_sub_to₂ : Ioo (-ε) 0 ⊆ Ioo (-ε₂) 0 := by
          intro y hy
          have hy_right : y < 0 := hy.2
          have hε_le_ε₂ : ε ≤ ε₂ := min_le_right _ _
          have hneg_le : -ε₂ ≤ -ε := neg_le_neg hε_le_ε₂
          have hy_left : -ε₂ < y := lt_of_le_of_lt hneg_le hy.1
          exact ⟨hy_left, hy_right⟩
        -- Step 2.2.1.3.5: Combine with the inductive subsets to obtain containment in `s ∩ t`.
        have h_sub_s : Ioo (-ε) 0 ⊆ s := fun y hy => h_sub₁ (h_sub_to₁ hy)
        have h_sub_t : Ioo (-ε) 0 ⊆ t := fun y hy => h_sub₂ (h_sub_to₂ hy)
        refine ⟨ε, hε_pos, ?_⟩
        intro y hy
        exact ⟨h_sub_s hy, h_sub_t hy⟩
    | sUnion S hS ihS =>
        -- Step 2.2.1.4: Inductive step – arbitrary unions of generated opens.
        intro h0
        -- Step 2.2.1.4.1: Choose a member `V ∈ S` that contains `0`.
        rcases mem_sUnion.mp h0 with ⟨V, hVS, h0V⟩
        -- Step 2.2.1.4.2: Apply the induction hypothesis to this `V`.
        rcases ihS V hVS h0V with ⟨ε, hε_pos, h_sub⟩
        -- Step 2.2.1.4.3: The same interval `(-ε,0)` lies inside the whole union.
        refine ⟨ε, hε_pos, ?_⟩
        intro y hy
        exact mem_sUnion.mpr ⟨V, hVS, h_sub hy⟩

  -- Step 2.3: Package the lemma above in terms of `K_topology.IsOpen`.
  have h_Ktop_open_zero_has_neg_interval :
      ∀ {U : Set ℝ}, K_topology.IsOpen U → (0 : ℝ) ∈ U →
        ∃ ε > (0 : ℝ), Ioo (-ε) 0 ⊆ U := by
    intro U hU h0U
    -- Step 2.3.1: Reinterpret `IsOpen` in `K_topology` as a `GenerateOpen` statement.
    have hU_gen : TopologicalSpace.GenerateOpen g U := by
      -- `IsOpen` for a `generateFrom g` topology is definitionally `GenerateOpen g`.
      simpa [h_Ktop_def] using hU
    -- Step 2.3.2: Apply the inductive lemma from Step 2.2.
    exact h_K_open_zero_has_neg_interval hU_gen h0U

  -- Step 2.4: Use the interval lemma to show that `[0,1)` is not open in `K_topology`.
  have h_not_K_open_Ico : ¬ K_topology.IsOpen (Ico (0 : ℝ) 1) := by
    -- Step 2.4.1: Argue by contradiction.
    intro h_open
    -- Step 2.4.2: Note that `0` lies in `[0,1)`.
    have h0_mem : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := by
      -- `0 ≤ 0` and `0 < 1`.
      exact ⟨le_rfl, by norm_num⟩
    -- Step 2.4.3: Apply the lemma from Step 2.3 specialized to `U = [0,1)`.
    rcases h_Ktop_open_zero_has_neg_interval h_open h0_mem with ⟨ε, hε_pos, h_sub⟩
    -- Step 2.4.4: Choose a point `y` with `-ε < y < 0` using density of the reals.
    obtain ⟨y, hy_mem_Ioo⟩ :
        ∃ y : ℝ, y ∈ Ioo (-ε) 0 := by
      -- Step 2.4.4.1: First note that `-ε < 0` since `ε > 0`.
      have h_neg_lt_zero : -ε < (0 : ℝ) := by
        simpa using (neg_lt_zero.mpr hε_pos)
      -- Step 2.4.4.2: Use `exists_between` to pick `y` with `-ε < y < 0`.
      rcases exists_between h_neg_lt_zero with ⟨y, hy⟩
      exact ⟨y, hy⟩
    -- Step 2.4.5: The subset property sends this `y` into `[0,1)`, contradicting its negativity.
    have hy_in_Ico : y ∈ Ico (0 : ℝ) 1 := h_sub hy_mem_Ioo
    have hy_nonneg : (0 : ℝ) ≤ y := hy_in_Ico.1
    have hy_neg : y < 0 := hy_mem_Ioo.2
    exact (not_le_of_gt hy_neg) hy_nonneg

  -- Step 3: Use `[0,1)` as a counterexample to the inclusion
  --         `∀ U, Rl.IsOpen U → K_topology.IsOpen U`.
  --         This shows that `K_topology` is not finer than `Rl`.
  have h_not_all_Rl_to_K :
      ¬ (∀ U, Rl.IsOpen U → K_topology.IsOpen U) := by
    -- Step 3.1: Suppose every `Rl`-open set were `K_topology`-open.
    intro h
    -- Step 3.2: Apply this to the particular set `[0,1)`.
    have h_open_K : K_topology.IsOpen (Ico (0 : ℝ) 1) := h _ h_Rl_open_Ico
    -- Step 3.3: This contradicts Step 2.4.
    exact h_not_K_open_Ico h_open_K

  -- Step 4: Show that `(-1,1) \ K` is open in `K_topology`.
  have h_K_open_Ioo_diff :
      K_topology.IsOpen (Ioo (-1 : ℝ) 1 \ K) := by
    -- Step 4.1: Prove membership of `(-1,1) \ K` in the generating family `g`.
    have h_mem_gen :
        Ioo (-1 : ℝ) 1 \ K ∈ g := by
      -- Step 4.1.1: It lies in the second part of the union, with `a = -1`, `b = 1`.
      have h_in_right :
          Ioo (-1 : ℝ) 1 \ K ∈
            {S : Set ℝ | ∃ a b, a < b ∧ S = Ioo a b \ K} := by
        exact ⟨(-1 : ℝ), 1, by norm_num, rfl⟩
      -- Step 4.1.2: Inject this into the full union `g`.
      exact Or.inr h_in_right
    -- Step 4.2: Convert membership in the generating family into openness.
    have : IsOpen[TopologicalSpace.generateFrom g] (Ioo (-1 : ℝ) 1 \ K) :=
      TopologicalSpace.isOpen_generateFrom_of_mem h_mem_gen
    simpa [h_Ktop_def] using this

  -- Step 5: Show that `0` belongs to `(-1,1) \ K` with the corrected definition of `K`.
  have h0_not_in_K : (0 : ℝ) ∉ K := by
    -- Step 5.1: Argue by contradiction.
    intro h0K
    rcases h0K with ⟨n, h0_eq⟩
    -- Step 5.2: `1 / (n + 1)` is strictly positive.
    have h_pos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by
      -- `n + 1` is a positive real, so its reciprocal is positive.
      have h_nat_pos : 0 < (n + 1 : ℝ) := by
        exact_mod_cast (Nat.succ_pos n)
      exact (one_div_pos.mpr h_nat_pos)
    -- Step 5.3: Combine with `0 = 1 / (n + 1)` to deduce `0 < 0`, a contradiction.
    have : (0 : ℝ) < 0 := by simp [h0_eq] at h_pos
    exact lt_irrefl _ this

  have h0_in_Ioo_diff : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 \ K := by
    -- Step 5.4: `0` lies in `(-1,1)` but not in `K`.
    have h0_in_Ioo : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by
      -- `-1 < 0` and `0 < 1`.
      exact ⟨by norm_num, by norm_num⟩
    exact ⟨h0_in_Ioo, h0_not_in_K⟩

  -- Step 6: Establish the corresponding "positivity near 0" lemma
  --         for the lower-limit topology `Rl`.
  --         Any `Rl`-open set containing `0` must contain some `[0,δ)`.
  have h_Rl_open_zero_has_pos_interval :
      ∀ {U : Set ℝ},
        TopologicalSpace.GenerateOpen
          {S : Set ℝ | ∃ a b, a < b ∧ S = Ico a b} U →
        (0 : ℝ) ∈ U →
        ∃ δ > (0 : ℝ), Ico (0 : ℝ) δ ⊆ U := by
    -- Step 6.1: Again use induction on the `GenerateOpen` derivation.
    intro U hU
    induction hU with
    | basic s hs =>
        -- Step 6.1.1: Base case – `U` is one of the generating sets `s = [a,b)`.
        intro h0s
        -- Step 6.1.1.1: Unpack `s` as a concrete interval `[a,b)`.
        rcases hs with ⟨a, b, hab, rfl⟩
        -- Step 6.1.1.2: Use `0 ∈ [a,b)` to get `a ≤ 0` and `0 < b`.
        rcases h0s with ⟨ha0, h0b⟩
        -- Step 6.1.1.3: Take `δ = b`, which is strictly positive.
        refine ⟨b, h0b, ?_⟩
        -- Step 6.1.1.4: Show `[0,b) ⊆ [a,b)`.
        intro y hy
        have hy_nonneg : (0 : ℝ) ≤ y := hy.1
        have hy_lt_b : y < b := hy.2
        -- Since `a ≤ 0 ≤ y`, we obtain `a ≤ y`.
        have hay : a ≤ y := le_trans ha0 hy_nonneg
        exact ⟨hay, hy_lt_b⟩
    | univ =>
        -- Step 6.1.2: Base case – `U = univ`.
        intro _h0
        -- Step 6.1.2.1: Take `δ = 1`, which is positive.
        refine ⟨(1 : ℝ), by norm_num, ?_⟩
        -- Step 6.1.2.2: `[0,1)` is obviously contained in `univ`.
        intro _y _hy
        trivial
    | inter s t hs ht ihs iht =>
        -- Step 6.1.3: Inductive step – intersections.
        intro h0st
        -- Step 6.1.3.1: Split the membership `0 ∈ s ∩ t`.
        rcases h0st with ⟨h0s, h0t⟩
        -- Step 6.1.3.2: Apply the induction hypotheses to obtain intervals for `s` and `t`.
        rcases ihs h0s with ⟨δ₁, hδ₁_pos, h_sub₁⟩
        rcases iht h0t with ⟨δ₂, hδ₂_pos, h_sub₂⟩
        -- Step 6.1.3.3: Work with the smaller radius.
        let δ := min δ₁ δ₂
        have hδ_pos : (0 : ℝ) < δ := by
          exact (lt_min_iff).2 ⟨hδ₁_pos, hδ₂_pos⟩
        -- Step 6.1.3.4: Show `[0,δ) ⊆ [0,δ₁)` and `[0,δ) ⊆ [0,δ₂)`.
        have h_sub_to₁ : Ico (0 : ℝ) δ ⊆ Ico (0 : ℝ) δ₁ := by
          intro y hy
          have hy_nonneg : (0 : ℝ) ≤ y := hy.1
          have hδ_le : δ ≤ δ₁ := min_le_left _ _
          have hy_lt_δ₁ : y < δ₁ := lt_of_lt_of_le hy.2 hδ_le
          exact ⟨hy_nonneg, hy_lt_δ₁⟩
        have h_sub_to₂ : Ico (0 : ℝ) δ ⊆ Ico (0 : ℝ) δ₂ := by
          intro y hy
          have hy_nonneg : (0 : ℝ) ≤ y := hy.1
          have hδ_le : δ ≤ δ₂ := min_le_right _ _
          have hy_lt_δ₂ : y < δ₂ := lt_of_lt_of_le hy.2 hδ_le
          exact ⟨hy_nonneg, hy_lt_δ₂⟩
        -- Step 6.1.3.5: Combine both containments to get `[0,δ) ⊆ s ∩ t`.
        have h_sub_s : Ico (0 : ℝ) δ ⊆ s := fun y hy => h_sub₁ (h_sub_to₁ hy)
        have h_sub_t : Ico (0 : ℝ) δ ⊆ t := fun y hy => h_sub₂ (h_sub_to₂ hy)
        refine ⟨δ, hδ_pos, ?_⟩
        intro y hy
        exact ⟨h_sub_s hy, h_sub_t hy⟩
    | sUnion S hS ihS =>
        -- Step 6.1.4: Inductive step – arbitrary unions.
        intro h0
        -- Step 6.1.4.1: Pick a member `V ∈ S` containing `0`.
        rcases mem_sUnion.mp h0 with ⟨V, hVS, h0V⟩
        -- Step 6.1.4.2: Apply the induction hypothesis to this `V`.
        rcases ihS V hVS h0V with ⟨δ, hδ_pos, h_sub⟩
        -- Step 6.1.4.3: The same interval `[0,δ)` lies inside the whole union.
        refine ⟨δ, hδ_pos, ?_⟩
        intro y hy
        exact mem_sUnion.mpr ⟨V, hVS, h_sub hy⟩

  -- Step 6.2: Repackage the lemma in terms of `Rl.IsOpen`.
  have h_Rl_open_zero_has_pos_interval' :
      ∀ {U : Set ℝ}, Rl.IsOpen U → (0 : ℝ) ∈ U →
        ∃ δ > (0 : ℝ), Ico (0 : ℝ) δ ⊆ U := by
    intro U hU h0U
    -- Step 6.2.1: Interpret `Rl.IsOpen` via `GenerateOpen` for the lower-limit generators.
    have hU_gen :
        TopologicalSpace.GenerateOpen
          {S : Set ℝ | ∃ a b, a < b ∧ S = Ico a b} U := by
      simpa [Rl, lower_limit_topology] using hU
    -- Step 6.2.2: Apply the inductive lemma.
    exact h_Rl_open_zero_has_pos_interval hU_gen h0U

  -- Step 7: Use the interval lemma to show that `(-1,1) \ K` is not open in the lower-limit topology.
  have h_not_Rl_open_Ioo_diff :
      ¬ Rl.IsOpen (Ioo (-1 : ℝ) 1 \ K) := by
    -- Step 7.1: Argue by contradiction.
    intro h_open
    -- Step 7.2: Apply the positive-interval lemma at the point `0`.
    rcases h_Rl_open_zero_has_pos_interval' h_open h0_in_Ioo_diff with
      ⟨δ, hδ_pos, h_sub⟩
    -- Step 7.3: Use the Archimedean property to find a point of `K` inside `[0,δ)`.
    --           We take some `1 / (n + 1)` smaller than `δ`.
    have hδ_pos' : 0 < δ := hδ_pos
    obtain ⟨n, h_n_lt⟩ :=
      (exists_nat_one_div_lt (K := ℝ) hδ_pos')
    -- Step 7.4: The point `x = 1 / (n + 1)` belongs to `K`.
    let x : ℝ := 1 / (n + 1 : ℝ)
    have hx_in_K : x ∈ K := by
      -- Directly by definition of `K`.
      exact ⟨n, rfl⟩
    -- Step 7.5: Show that `x` lies in `[0,δ)`.
    have hx_in_Ico : x ∈ Ico (0 : ℝ) δ := by
      -- Step 7.5.1: Nonnegativity `0 ≤ x`.
      have hx_nonneg : (0 : ℝ) ≤ x := by
        have h_nat_nonneg : (0 : ℝ) ≤ (n + 1 : ℝ) := by
          exact_mod_cast (Nat.zero_le (n + 1))
        have h_div_nonneg : (0 : ℝ) ≤ 1 / (n + 1 : ℝ) :=
          (one_div_nonneg.mpr h_nat_nonneg)
        simpa [x] using h_div_nonneg
      -- Step 7.5.2: Strict inequality `x < δ` from the Archimedean bound.
      have hx_lt_δ : x < δ := by
        simpa [x] using h_n_lt
      exact ⟨hx_nonneg, hx_lt_δ⟩
    -- Step 7.6: Use the subset property to see that `x` lies in `(-1,1) \ K`.
    have hx_in_diff : x ∈ Ioo (-1 : ℝ) 1 \ K := by
      -- Since `x ∈ [0,δ)` and `[0,δ) ⊆ (-1,1) \ K`, membership follows.
      exact h_sub hx_in_Ico
    -- Step 7.7: But by construction `x ∈ K`, contradicting the definition of the difference.
    exact hx_in_diff.2 hx_in_K

  -- Step 8: Use `(-1,1) \ K` as a counterexample to the inclusion
  --         `∀ U, K_topology.IsOpen U → Rl.IsOpen U`.
  have h_not_all_K_to_Rl :
      ¬ (∀ U, K_topology.IsOpen U → Rl.IsOpen U) := by
    -- Step 8.1: Suppose every `K_topology`-open set were `Rl`-open.
    intro h
    -- Step 8.2: Apply this to `(-1,1) \ K`, which is open in `K_topology`.
    have h_open_Rl : Rl.IsOpen (Ioo (-1 : ℝ) 1 \ K) := h _ h_K_open_Ioo_diff
    -- Step 8.3: This contradicts Step 7.
    exact h_not_Rl_open_Ioo_diff h_open_Rl

  -- Step 9: Combine the two negations to prove the original statement.
  exact ⟨h_not_all_Rl_to_K, h_not_all_K_to_Rl⟩
