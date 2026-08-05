import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Let $A$ be a proper subset of $X$, and let $B$ be a proper subset of $Y$. If $X$ and $Y$ are connected, show that $(X \times Y)-(A \times B)$ is connected.
-/

/-Informal Proof

This is similar to the proof of Theorem 23.6. Take $c \times d \in(X \backslash A) \times(Y \backslash B)$. For each $x \in X \backslash A$, the set
$$
U_x=(X \times\{d\}) \cup(\{x\} \times Y)
$$
is connected since $X \times\{d\}$ and $\{x\} \times Y$ are connected and have the common point $x \times d$. Then $U=\bigcup_{x \in X \backslash A} U_x$ is connected because it is the union of the connected spaces $U_x$ which have the point $c \times d$ in common. Similarly, for each $y \in Y \backslash B$ the set
$$
V_y=(X \times\{y\}) \cup(\{c\} \times Y)
$$
is connected, so $V=\bigcup_{y \in Y \backslash B} V_y$ is connected. Thus $(X \times Y) \backslash(A \times B)=U \cup V$ is connected since $c \times d$ is a common point of $U$ and $V$.
-/

theorem Munkres_exercise_23_9 {X Y : Type*}
  [TopologicalSpace X] [TopologicalSpace Y]
  (A₁ A₂ : Set X)
  (B₁ B₂ : Set Y)
  (hA : A₁ ⊂ A₂)
  (hB : B₁ ⊂ B₂)
  (hA : IsConnected A₂)
  (hB : IsConnected B₂) :
  IsConnected ({x | ∃ a b, x = (a, b) ∧ a ∈ A₂ ∧ b ∈ B₂} \
      {x | ∃ a b, x = (a, b) ∧ a ∈ A₁ ∧ b ∈ B₁}) := by
  classical
  -- Step 1: record the hypotheses under convenient names and rewrite the product sets explicitly.
  have hA_ss : A₁ ⊂ A₂ := ‹A₁ ⊂ A₂›
  -- Step 1.1: mirror the strict-containment hypothesis on the Y-factor.
  have hB_ss : B₁ ⊂ B₂ := ‹B₁ ⊂ B₂›
  -- Step 1.2: keep the connectedness assumptions handy.
  have hA_conn : IsConnected A₂ := ‹IsConnected A₂›
  have hB_conn : IsConnected B₂ := ‹IsConnected B₂›
  -- Step 1.3: turn the first comprehension set into the usual cartesian product.
  have hProdA :
      {x | ∃ a b, x = (a, b) ∧ a ∈ A₂ ∧ b ∈ B₂} = A₂ ×ˢ B₂ := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨a, b, rfl, ha, hb⟩
      exact ⟨ha, hb⟩
    · intro hx
      rcases x with ⟨x₁, x₂⟩
      rcases hx with ⟨hx₁, hx₂⟩
      exact ⟨x₁, x₂, rfl, hx₁, hx₂⟩
  -- Step 1.4: perform the same rewrite for the second comprehension set.
  have hProdB :
      {x | ∃ a b, x = (a, b) ∧ a ∈ A₁ ∧ b ∈ B₁} = A₁ ×ˢ B₁ := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨a, b, rfl, ha, hb⟩
      exact ⟨ha, hb⟩
    · intro hx
      rcases x with ⟨x₁, x₂⟩
      rcases hx with ⟨hx₁, hx₂⟩
      exact ⟨x₁, x₂, rfl, hx₁, hx₂⟩
  -- Step 1.5: reduce the goal to proving the cartesian-product version.
  suffices IsConnected ((A₂ ×ˢ B₂) \ (A₁ ×ˢ B₁)) by
    simpa [hProdA, hProdB]
  -- Step 2: pick witnesses living outside the smaller sets to serve as anchors.
  obtain ⟨c, hcA₂, hcNotA₁⟩ := Set.not_subset.1 hA_ss.not_subset
  obtain ⟨d, hdB₂, hdNotB₁⟩ := Set.not_subset.1 hB_ss.not_subset
  -- Step 3: name the target set succinctly and record that the anchor point belongs to it.
  set T := (A₂ ×ˢ B₂) \ (A₁ ×ˢ B₁) with hT_def
  -- Step 3.1: verify that the chosen anchor `(c, d)` indeed lies in `T`.
  have hBase : (c, d) ∈ T := by
    simp [T, hcA₂, hdB₂, hcNotA₁, hdNotB₁]
  -- Step 4: assemble the family of “cross” subsets whose union equals the target set.
  let ℱ₁ : Set (Set (X × Y)) :=
    {S | ∃ x ∈ A₂ \ A₁, S = (A₂ ×ˢ {d}) ∪ ({x} ×ˢ B₂)}
  let ℱ₂ : Set (Set (X × Y)) :=
    {S | ∃ y ∈ B₂ \ B₁, S = (A₂ ×ˢ {y}) ∪ ({c} ×ˢ B₂)}
  let ℱ := ℱ₁ ∪ ℱ₂
  -- Step 4.1: every element of the family contains the anchor point `(c, d)`.
  have hBase_mem : ∀ S ∈ ℱ, (c, d) ∈ S := by
    intro S hS
    rcases hS with hS | hS
    · rcases hS with ⟨x, _, rfl⟩
      simp [Set.mem_prod, hcA₂, hdB₂]
    · rcases hS with ⟨y, _, rfl⟩
      simp [Set.mem_prod, hcA₂, hdB₂]
  -- Step 4.2: each member of the family is preconnected (in fact connected).
  have hPreconnected : ∀ S ∈ ℱ, IsPreconnected S := by
    intro S hS
    rcases hS with hS | hS
    · rcases hS with ⟨x, hx, rfl⟩
      -- Step 4.2.1: the horizontal and vertical pieces meeting at `(x, d)` are connected.
      have h1 : IsConnected (A₂ ×ˢ ({d} : Set Y)) :=
        hA_conn.prod (isConnected_singleton (x := d))
      have h2 : IsConnected (({x} : Set X) ×ˢ B₂) :=
        (isConnected_singleton (x := x)).prod hB_conn
      -- Step 4.2.2: the two pieces intersect at `(x, d)`, hence their union is connected.
      have hInt :
          ((A₂ ×ˢ ({d} : Set Y)) ∩ (({x} : Set X) ×ˢ B₂)).Nonempty := by
        refine ⟨(x, d), ?_⟩
        simp [Set.mem_prod, hx.1, hdB₂]
      exact (IsConnected.union hInt h1 h2).isPreconnected
    · rcases hS with ⟨y, hy, rfl⟩
      -- Step 4.2.3: the analogous statement holds for the vertical family.
      have h1 : IsConnected (A₂ ×ˢ ({y} : Set Y)) :=
        hA_conn.prod (isConnected_singleton (x := y))
      have h2 : IsConnected (({c} : Set X) ×ˢ B₂) :=
        (isConnected_singleton (x := c)).prod hB_conn
      have hInt :
          ((A₂ ×ˢ ({y} : Set Y)) ∩ (({c} : Set X) ×ˢ B₂)).Nonempty := by
        refine ⟨(c, y), ?_⟩
        simp [Set.mem_prod, hcA₂, hy.1]
      exact (IsConnected.union hInt h1 h2).isPreconnected
  -- Step 4.3: the target set `T` is exactly the union of this family.
  have hSub₁ : ⋃₀ ℱ ⊆ T := by
    intro z hz
    rcases z with ⟨z₁, z₂⟩
    rcases Set.mem_sUnion.1 hz with ⟨S, hS, hzS⟩
    rcases hS with hS | hS
    · rcases hS with ⟨x, hx, rfl⟩
      rcases hzS with hzS | hzS
      · have hzData : z₁ ∈ A₂ ∧ z₂ = d := by
          simpa [Set.mem_prod] using hzS
        have hzB₂ : z₂ ∈ B₂ := by simpa [hzData.2] using hdB₂
        have hzNot : ¬ (z₁ ∈ A₁ ∧ z₂ ∈ B₁) := by
          intro h
          have : z₂ ∈ B₁ := h.2
          exact hdNotB₁ (by simpa [hzData.2] using this)
        have hzIn : (z₁, z₂) ∈ T := by
          simp [T, Set.mem_prod, hzData.1, hzB₂, hzNot]
        simpa using hzIn
      · have hzData : z₁ = x ∧ z₂ ∈ B₂ := by
          simpa [Set.mem_prod] using hzS
        have hzA₂ : z₁ ∈ A₂ := by simpa [hzData.1] using hx.1
        have hzNot : ¬ (z₁ ∈ A₁ ∧ z₂ ∈ B₁) := by
          intro h
          exact hx.2 (by simpa [hzData.1] using h.1)
        have hzIn : (z₁, z₂) ∈ T := by
          simp [T, Set.mem_prod, hzA₂, hzData.2, hzNot]
        simpa using hzIn
    · rcases hS with ⟨y, hy, rfl⟩
      rcases hzS with hzS | hzS
      · have hzData : z₁ ∈ A₂ ∧ z₂ = y := by
          simpa [Set.mem_prod] using hzS
        have hzB₂ : z₂ ∈ B₂ := by simpa [hzData.2] using hy.1
        have hzNot : ¬ (z₁ ∈ A₁ ∧ z₂ ∈ B₁) := by
          intro h
          exact hy.2 (by simpa [hzData.2] using h.2)
        have hzIn : (z₁, z₂) ∈ T := by
          simp [T, Set.mem_prod, hzData.1, hzB₂, hzNot]
        simpa using hzIn
      · have hzData : z₁ = c ∧ z₂ ∈ B₂ := by
          simpa [Set.mem_prod] using hzS
        have hzNot : ¬ (z₁ ∈ A₁ ∧ z₂ ∈ B₁) := by
          intro h
          have : z₁ ∈ A₁ := h.1
          exact hcNotA₁ (by simpa [hzData.1] using this)
        have hzA₂ : z₁ ∈ A₂ := by simpa [hzData.1] using hcA₂
        have hzIn : (z₁, z₂) ∈ T := by
          simp [T, Set.mem_prod, hzA₂, hzData.2, hzNot]
        simpa using hzIn
  -- Step 4.3.1: show the opposite inclusion so that the union really equals `T`.
  have hSub₂ : T ⊆ ⋃₀ ℱ := by
    intro z hz
    rcases z with ⟨z₁, z₂⟩
    have hz' : (z₁, z₂) ∈ (A₂ ×ˢ B₂) \ (A₁ ×ˢ B₁) := by
      simpa [T] using hz
    have hzIn : (z₁, z₂) ∈ A₂ ×ˢ B₂ := hz'.1
    have hzNot : (z₁, z₂) ∉ A₁ ×ˢ B₁ := hz'.2
    have hzA₂ : z₁ ∈ A₂ := (Set.mem_prod.1 hzIn).1
    have hzB₂ : z₂ ∈ B₂ := (Set.mem_prod.1 hzIn).2
    have hzNot' : ¬ (z₁ ∈ A₁ ∧ z₂ ∈ B₁) := by
      simpa [Set.mem_prod] using hzNot
    classical
    by_cases hzA₁ : z₁ ∈ A₁
    · have hzNotB₁ : z₂ ∉ B₁ := by
        intro hzB₁
        exact hzNot' ⟨hzA₁, hzB₁⟩
      have hzB₂Diff : z₂ ∈ B₂ \ B₁ := ⟨hzB₂, hzNotB₁⟩
      refine Set.mem_sUnion.2 ?_
      refine ⟨(A₂ ×ˢ ({z₂} : Set Y)) ∪ (({c} : Set X) ×ˢ B₂), ?_, ?_⟩
      · exact Or.inr ⟨z₂, hzB₂Diff, rfl⟩
      · have hzMem : (z₁, z₂) ∈ A₂ ×ˢ ({z₂} : Set Y) := by
          simp [Set.mem_prod, hzA₂]
        exact Or.inl hzMem
    · have hzA₂Diff : z₁ ∈ A₂ \ A₁ := ⟨hzA₂, hzA₁⟩
      refine Set.mem_sUnion.2 ?_
      refine ⟨(A₂ ×ˢ {d}) ∪ (({z₁} : Set X) ×ˢ B₂), ?_, ?_⟩
      · exact Or.inl ⟨z₁, hzA₂Diff, rfl⟩
      · have hzMem : (z₁, z₂) ∈ ({z₁} : Set X) ×ˢ B₂ := by
          simp [Set.mem_prod, hzB₂]
        exact Or.inr hzMem
  have hUnion_eq : ⋃₀ ℱ = T := Set.Subset.antisymm hSub₁ hSub₂
  -- Step 5: gather connectedness of the union and transfer it to `T`.
  have hUnion_pre : IsPreconnected (⋃₀ ℱ) :=
    isPreconnected_sUnion (c, d) ℱ hBase_mem hPreconnected
  -- Step 5.1: the union is nonempty since it contains the anchor.
  have hUnion_nonempty : (⋃₀ ℱ).Nonempty := by
    refine ⟨(c, d), ?_⟩
    refine Set.mem_sUnion.2 ?_
    refine ⟨(A₂ ×ˢ {d}) ∪ (({c} : Set X) ×ˢ B₂), ?_, ?_⟩
    · exact Or.inl ⟨c, ⟨hcA₂, hcNotA₁⟩, rfl⟩
    · simp [Set.mem_prod, hcA₂]
  -- Step 5.2: conclude that the union—and hence `T`—is connected.
  have hUnion_conn : IsConnected (⋃₀ ℱ) := ⟨hUnion_nonempty, hUnion_pre⟩
  have hT_conn : IsConnected T := by
    simpa [hUnion_eq] using hUnion_conn
  -- Step 6: translate the result back to the original statement.
  simpa [T] using hT_conn



/-
The original formalization (`Munkres_exercise_23_9`) is a strict generalization of the
informal statement. It replaces the ambient connected spaces X, Y with arbitrary connected
subsets A₂, B₂, and asks for (A₂ ×ˢ B₂) \ (A₁ ×ˢ B₁) to be connected given A₁ ⊂ A₂
and B₁ ⊂ B₂. While specializing A₂ = univ, B₂ = univ recovers the informal claim, the
Lean version asserts the result for arbitrary connected subsets, which is logically stronger.

The corrected version below directly encodes the informal statement: X and Y are connected
spaces, A ⊊ X, B ⊊ Y, and the conclusion is that (X × Y) \ (A × B) is connected.
-/
theorem Munkres_exercise_23_9_corrected {X Y : Type*}
  [TopologicalSpace X] [TopologicalSpace Y]
  (A : Set X) (B : Set Y)
  (hA : A ⊂ (Set.univ : Set X))
  (hB : B ⊂ (Set.univ : Set Y))
  (hX : IsConnected (Set.univ : Set X))
  (hY : IsConnected (Set.univ : Set Y)) :
  IsConnected ((Set.univ : Set (X × Y)) \ (A ×ˢ B)) := by
  -- Step 1: Pick a point c ∈ X \ A and d ∈ Y \ B to serve as the anchor.
  -- Step 1.1: Extract c ∉ A from the strict subset hypothesis.
  obtain ⟨c, _, hcA⟩ := Set.not_subset.1 hA.not_subset
  -- Step 1.2: Extract d ∉ B from the strict subset hypothesis.
  obtain ⟨d, _, hdB⟩ := Set.not_subset.1 hB.not_subset
  -- Step 2: Name the target set T = univ \ (A ×ˢ B) and verify (c, d) ∈ T.
  set T := (Set.univ : Set (X × Y)) \ (A ×ˢ B) with hT_def
  -- Step 2.1: The anchor (c, d) lies in T since c ∉ A.
  have hBase : (c, d) ∈ T := by
    simp [T, Set.mem_prod, hcA]
  -- Step 3: Define two families of cross-shaped connected sets.
  -- For each x ∈ X \ A, the "horizontal + vertical" cross through (x, d):
  --   U_x = (univ ×ˢ {d}) ∪ ({x} ×ˢ univ)
  -- For each y ∈ Y \ B, the "horizontal + vertical" cross through (c, y):
  --   V_y = (univ ×ˢ {y}) ∪ ({c} ×ˢ univ)
  let ℱ₁ : Set (Set (X × Y)) :=
    {S | ∃ x ∈ Set.univ \ A, S = (Set.univ ×ˢ {d}) ∪ ({x} ×ˢ Set.univ)}
  let ℱ₂ : Set (Set (X × Y)) :=
    {S | ∃ y ∈ Set.univ \ B, S = (Set.univ ×ˢ {y}) ∪ ({c} ×ˢ Set.univ)}
  let ℱ := ℱ₁ ∪ ℱ₂
  -- Step 4: Show every member of ℱ contains the anchor (c, d).
  have hBase_mem : ∀ S ∈ ℱ, (c, d) ∈ S := by
    intro S hS
    rcases hS with hS | hS
    -- Step 4.1: For S ∈ ℱ₁, (c, d) ∈ univ ×ˢ {d} ⊆ S.
    · rcases hS with ⟨x, _, rfl⟩
      exact Or.inl ⟨Set.mem_univ c, rfl⟩
    -- Step 4.2: For S ∈ ℱ₂, (c, d) ∈ {c} ×ˢ univ ⊆ S.
    · rcases hS with ⟨y, _, rfl⟩
      exact Or.inr ⟨rfl, Set.mem_univ d⟩
  -- Step 5: Show every member of ℱ is preconnected.
  have hPreconnected : ∀ S ∈ ℱ, IsPreconnected S := by
    intro S hS
    rcases hS with hS | hS
    · -- Step 5.1: Case S ∈ ℱ₁, i.e., S = (univ ×ˢ {d}) ∪ ({x} ×ˢ univ) for some x ∉ A.
      rcases hS with ⟨x, hx, rfl⟩
      -- Step 5.1.1: The horizontal slice univ ×ˢ {d} is connected (product of connected and singleton).
      have h1 : IsConnected (Set.univ ×ˢ ({d} : Set Y)) :=
        hX.prod (isConnected_singleton (x := d))
      -- Step 5.1.2: The vertical slice {x} ×ˢ univ is connected (product of singleton and connected).
      have h2 : IsConnected (({x} : Set X) ×ˢ Set.univ) :=
        (isConnected_singleton (x := x)).prod hY
      -- Step 5.1.3: They intersect at (x, d), so their union is connected.
      have hInt : ((Set.univ ×ˢ ({d} : Set Y)) ∩ (({x} : Set X) ×ˢ Set.univ)).Nonempty := by
        exact ⟨(x, d), ⟨Set.mem_univ x, rfl⟩, ⟨rfl, Set.mem_univ d⟩⟩
      exact (IsConnected.union hInt h1 h2).isPreconnected
    · -- Step 5.2: Case S ∈ ℱ₂, i.e., S = (univ ×ˢ {y}) ∪ ({c} ×ˢ univ) for some y ∉ B.
      rcases hS with ⟨y, hy, rfl⟩
      -- Step 5.2.1: The horizontal slice univ ×ˢ {y} is connected.
      have h1 : IsConnected (Set.univ ×ˢ ({y} : Set Y)) :=
        hX.prod (isConnected_singleton (x := y))
      -- Step 5.2.2: The vertical slice {c} ×ˢ univ is connected.
      have h2 : IsConnected (({c} : Set X) ×ˢ Set.univ) :=
        (isConnected_singleton (x := c)).prod hY
      -- Step 5.2.3: They intersect at (c, y), so their union is connected.
      have hInt : ((Set.univ ×ˢ ({y} : Set Y)) ∩ (({c} : Set X) ×ˢ Set.univ)).Nonempty := by
        exact ⟨(c, y), ⟨Set.mem_univ c, rfl⟩, ⟨rfl, Set.mem_univ y⟩⟩
      exact (IsConnected.union hInt h1 h2).isPreconnected
  -- Step 6: Show ⋃₀ ℱ ⊆ T (every cross avoids A ×ˢ B).
  have hSub₁ : ⋃₀ ℱ ⊆ T := by
    intro z hz
    rcases z with ⟨z₁, z₂⟩
    rcases Set.mem_sUnion.1 hz with ⟨S, hS, hzS⟩
    simp only [T, Set.mem_diff, Set.mem_univ, Set.mem_prod, true_and]
    rcases hS with hS | hS
    · -- Step 6.1: z ∈ S for some S ∈ ℱ₁, i.e., S = (univ ×ˢ {d}) ∪ ({x} ×ˢ univ), x ∉ A.
      rcases hS with ⟨x, hx, rfl⟩
      rcases hzS with hzS | hzS
      · -- Step 6.1.1: z ∈ univ ×ˢ {d}, so z₂ = d ∉ B, hence z ∉ A ×ˢ B.
        have hzd : z₂ = d := hzS.2
        intro ⟨_, hz₂B⟩
        exact hdB (hzd ▸ hz₂B)
      · -- Step 6.1.2: z ∈ {x} ×ˢ univ, so z₁ = x ∉ A, hence z ∉ A ×ˢ B.
        have hzx : z₁ = x := hzS.1
        intro ⟨hz₁A, _⟩
        exact hx.2 (hzx ▸ hz₁A)
    · -- Step 6.2: z ∈ S for some S ∈ ℱ₂, i.e., S = (univ ×ˢ {y}) ∪ ({c} ×ˢ univ), y ∉ B.
      rcases hS with ⟨y, hy, rfl⟩
      rcases hzS with hzS | hzS
      · -- Step 6.2.1: z ∈ univ ×ˢ {y}, so z₂ = y ∉ B, hence z ∉ A ×ˢ B.
        have hzy : z₂ = y := hzS.2
        intro ⟨_, hz₂B⟩
        exact hy.2 (hzy ▸ hz₂B)
      · -- Step 6.2.2: z ∈ {c} ×ˢ univ, so z₁ = c ∉ A, hence z ∉ A ×ˢ B.
        have hzc : z₁ = c := hzS.1
        intro ⟨hz₁A, _⟩
        exact hcA (hzc ▸ hz₁A)
  -- Step 7: Show T ⊆ ⋃₀ ℱ (every point of T lies in some cross).
  have hSub₂ : T ⊆ ⋃₀ ℱ := by
    intro z hz
    rcases z with ⟨z₁, z₂⟩
    have hzT : (z₁, z₂) ∈ T := hz
    -- Step 7.1: Since (z₁, z₂) ∉ A ×ˢ B, either z₁ ∉ A or z₂ ∉ B.
    have hzNot : ¬ (z₁ ∈ A ∧ z₂ ∈ B) := by
      simpa [T, Set.mem_prod] using hzT.2
    rcases not_and_or.mp hzNot with hz₁ | hz₂
    · -- Step 7.2: If z₁ ∉ A, then (z₁, z₂) lies in the cross U_{z₁} ∈ ℱ₁.
      refine Set.mem_sUnion.2 ⟨(Set.univ ×ˢ {d}) ∪ ({z₁} ×ˢ Set.univ), ?_, ?_⟩
      -- Step 7.2.1: The cross U_{z₁} is in ℱ₁ since z₁ ∈ univ \ A.
      · exact Or.inl ⟨z₁, ⟨Set.mem_univ z₁, hz₁⟩, rfl⟩
      -- Step 7.2.2: (z₁, z₂) ∈ {z₁} ×ˢ univ ⊆ U_{z₁}.
      · exact Or.inr ⟨rfl, Set.mem_univ z₂⟩
    · -- Step 7.3: If z₂ ∉ B, then (z₁, z₂) lies in the cross V_{z₂} ∈ ℱ₂.
      refine Set.mem_sUnion.2 ⟨(Set.univ ×ˢ {z₂}) ∪ ({c} ×ˢ Set.univ), ?_, ?_⟩
      -- Step 7.3.1: The cross V_{z₂} is in ℱ₂ since z₂ ∈ univ \ B.
      · exact Or.inr ⟨z₂, ⟨Set.mem_univ z₂, hz₂⟩, rfl⟩
      -- Step 7.3.2: (z₁, z₂) ∈ univ ×ˢ {z₂} ⊆ V_{z₂}.
      · exact Or.inl ⟨Set.mem_univ z₁, rfl⟩
  -- Step 8: Combine the two inclusions to get ⋃₀ ℱ = T.
  have hUnion_eq : ⋃₀ ℱ = T := Set.Subset.antisymm hSub₁ hSub₂
  -- Step 9: Conclude that ⋃₀ ℱ is connected (union of preconnected sets sharing the anchor).
  have hUnion_pre : IsPreconnected (⋃₀ ℱ) :=
    isPreconnected_sUnion (c, d) ℱ hBase_mem hPreconnected
  -- Step 9.1: ⋃₀ ℱ is nonempty since it contains (c, d).
  have hUnion_nonempty : (⋃₀ ℱ).Nonempty := ⟨(c, d), hUnion_eq ▸ hBase⟩
  -- Step 9.2: Combine nonemptiness and preconnectedness into connectedness.
  have hUnion_conn : IsConnected (⋃₀ ℱ) := ⟨hUnion_nonempty, hUnion_pre⟩
  -- Step 10: Transfer connectedness from ⋃₀ ℱ to T via the equality.
  simpa [hUnion_eq] using hUnion_conn
