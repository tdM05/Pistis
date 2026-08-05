import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Let $X$ be a compact Hausdorff space. Let $\mathcal{A}$ be a collection of closed connected subsets of $X$ that is simply ordered by proper inclusion. Then $Y=\bigcap_{A \in \mathcal{A}} A$ is connected.
-/

/-Informal Proof

Since each $A \in \mathcal{A}$ is closed, $Y$ is closed. Suppose that $C$ and $D$ form a separation of $Y$. Then $C$ and $D$ are closed in $Y$, hence closed in $X$. Since $X$ is compact, $C$ and $D$ are compact by Theorem 26.2. Since $X$ is Hausdorff, by Exercise 26.5, there exist $U$ and $V$ open in $X$ and disjoint containing $C$ and $D$, respectively. We show that
$$
\bigcap_{A \in \mathcal{A}}(A \backslash(U \cup V))
$$
is not empty. Let $\left\{A_1, \ldots, A_n\right\}$ be a finite subcollection of elements of $\mathcal{A}$. We may assume that $A_i \subsetneq A_{i+1}$ for all $i=1, \ldots, n-1$. Then
$$
\bigcap_{i=1}^n\left(A_i \backslash(U \cup V)\right)=A_1 \backslash(U \cup V) \text {. }
$$
Suppose that $A_1 \backslash(U \cup V)=\emptyset$. Then $A_1 \subset U \cup V$. Since $A_1$ is connected and $U \cap V=\emptyset, A_1$ lies within either $U$ or $V$, say $A_1 \subset U$. Then $Y \subset A_1 \subset U$, so that $C=Y \cap C \subset Y \cap V=\emptyset$, contradicting the fact that $C$ and $D$ form a separation of $Y$. Hence, $\bigcap_{i=1}^n\left(A_i \backslash(U \cup V)\right)$ is non-empty. Therefore, the collection $\{A \backslash(U \cup V) \mid A \in \mathcal{A}\}$ has the finite intersection property, so
$$
\bigcap_{A \in \mathcal{A}}(A \backslash(U \cup V))=\left(\bigcap_{A \in \mathcal{A}} A\right) \backslash(U \cup V)=Y \backslash(U \cup V)
$$
is non-empty. So there exists $y \in Y$ such that $y \notin U \cup V \supset C \cup D$, contradicting the fact that $C$ and $D$ form a separation of $Y$. We conclude that there is no such separation, so that $Y$ is connected.
-/

theorem Munkres_exercise_26_11
  {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  (A : Set (Set X)) (hA : ∀ (a b : Set X), a ∈ A → b ∈ A → a ⊆ b ∨ b ⊆ a)
  (hA' : ∀ a ∈ A, IsClosed a) (hA'' : ∀ a ∈ A, IsConnected a) :
  IsConnected (⋂₀ A) := by
  sorry

/-
Explanation of failure and missing premise:
Step 1: Consider `X = Bool` with its discrete topology; this space is compact and Hausdorff but disconnected.
Step 2: Take `A = ∅`. All hypotheses in the Lean statement hold vacuously, yet `⋂₀ A = Set.univ`, which is disconnected.
Step 3: The informal statement implicitly assumes that the family `𝓐` is nonempty; with that single extra premise, Munkres's compactness/finite-intersection-property argument carries through.
-/

/-- Negation of `Munkres_exercise_26_11`: the original statement fails for the empty chain in `Bool`. -/
theorem Munkres_exercise_26_11_neg :
  ¬ (∀ {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
        (A : Set (Set X))
        (_hA : ∀ (a b : Set X), a ∈ A → b ∈ A → a ⊆ b ∨ b ⊆ a)
        (_hA' : ∀ a ∈ A, IsClosed a) (_hA'' : ∀ a ∈ A, IsConnected a),
        IsConnected (⋂₀ A)) := by
  classical
  -- Step 1: Argue by contradiction and specialise the universal claim to `Bool`.
  intro h
  -- Step 1.0: Wrap the two-point space in `ULift` to avoid universe issues and equip it with the discrete topology.
  let X := ULift Bool
  letI : TopologicalSpace X := ⊥
  haveI : DiscreteTopology X := ⟨rfl⟩
  haveI : CompactSpace X := inferInstance
  haveI : T2Space X := inferInstance
  -- Step 1.1: Work with the empty chain inside this discrete compact Hausdorff space.
  set B : Set (Set X) := ∅
  -- Step 1.2: Record the vacuous hypotheses satisfied by the empty family.
  have hChain : ∀ (a b : Set X), a ∈ B → b ∈ B → a ⊆ b ∨ b ⊆ a := by
    intro a b ha _
    simp [B] at ha
  have hClosed : ∀ a ∈ B, IsClosed a := by
    intro a ha
    simp [B] at ha
  have hConnFam : ∀ a ∈ B, IsConnected a := by
    intro a ha
    simp [B] at ha
  have hBool := h (X := X) (A := B) hChain hClosed hConnFam
  -- Step 1.2: Prove that the universal claim forces `Set.univ : Set X` to be connected.
  -- Step 1.3: Exhibit the standard separation `{True}` and `{False}` to contradict connectedness.
  have hNotConn : ¬ IsConnected (Set.univ : Set X) := by
    -- Step 1.3.1: Assume towards contradiction that `Set.univ` is preconnected.
    intro hConn
    -- Step 1.3.2: Grant names to the clopen singletons used to separate the space.
    set U : Set X := {x | x.down = true}
    set V : Set X := {x | x.down = false}
    -- Step 1.3.3: Record that both singletons are open in the discrete topology.
    have hUopen : IsOpen U := isOpen_discrete _
    have hVopen : IsOpen V := isOpen_discrete _
    -- Step 1.3.4: Note that the union of the singletons covers the universe.
    have hCover : (Set.univ : Set X) ⊆ U ∪ V := by
      intro x _
      cases' x with b; cases b <;> simp [U, V]
    -- Step 1.3.5: Each singleton meets the universe, so the intersections are nonempty.
    have hUmeet : ((Set.univ : Set X) ∩ U).Nonempty := by
      refine ⟨⟨true⟩, ?_⟩
      simp [U]
    have hVmeet : ((Set.univ : Set X) ∩ V).Nonempty := by
      refine ⟨⟨false⟩, ?_⟩
      simp [V]
    -- Step 1.3.6: Invoke preconnectedness to deduce a point in the double intersection.
    have hIntersect :=
      hConn.isPreconnected U V hUopen hVopen hCover hUmeet hVmeet
    -- Step 1.3.7: Compute that the double intersection is empty, giving a contradiction.
    have hUVempty : U ∩ V = (∅ : Set X) := by
      ext x; cases' x with b; cases b <;> simp [U, V]
    have hEmpty : ¬ ((Set.univ : Set X) ∩ (U ∩ V)).Nonempty := by
      simp [hUVempty]
    exact hEmpty hIntersect
  -- Step 1.4: The forced connectedness contradicts the explicit separation, finishing the negation.
  exact hNotConn (by simpa [B] using hBool)

/-- Corrected statement: add nonemptiness of the chain (the only premise the informal
statement leaves implicit). The argument is the genuine Munkres proof: closedness in a
compact Hausdorff space, T2 separation of the disjoint compact pieces of a hypothetical
separation, and the finite intersection property (Cantor's theorem) applied to
`{ a \ (U ∪ V) : a ∈ A }`. -/
theorem Munkres_exercise_26_11_corrected
  {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  (A : Set (Set X)) (hAne : A.Nonempty)
  (hChain : ∀ (a b : Set X), a ∈ A → b ∈ A → a ⊆ b ∨ b ⊆ a)
  (hClosed : ∀ a ∈ A, IsClosed a) (hConn : ∀ a ∈ A, IsConnected a) :
  IsConnected (⋂₀ A) := by
  classical
  set Y : Set X := ⋂₀ A with hY_def
  -- Step 1: Basic facts: each `a` is nonempty/compact, and `Y` is closed/compact.
  have hA_ne : ∀ a ∈ A, a.Nonempty := fun a ha => (hConn a ha).nonempty
  have hA_compact : ∀ a ∈ A, IsCompact a := fun a ha => (hClosed a ha).isCompact
  have hY_closed : IsClosed Y := isClosed_sInter hClosed
  have hY_sub : ∀ a ∈ A, Y ⊆ a := fun a ha _ hx => hx a ha
  -- Step 2: The chain is directed downward under `⊇`.
  have hDir : DirectedOn (· ⊇ ·) A := by
    rintro a ha b hb
    rcases hChain a b ha hb with hab | hba
    · exact ⟨a, ha, Set.Subset.refl _, hab⟩
    · exact ⟨b, hb, hba, Set.Subset.refl _⟩
  -- Step 3: Cantor's intersection theorem gives `Y` nonempty.
  have hY_ne : Y.Nonempty := by
    haveI : Nonempty A := hAne.to_subtype
    exact IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
      hDir hA_ne hA_compact hClosed
  refine ⟨hY_ne, ?_⟩
  -- Step 4: Reduce preconnectedness to the closed-set formulation.
  rw [isPreconnected_closed_iff]
  intro C D hC hD hYsub hCmeet hDmeet
  -- Step 5: Suppose `Y ∩ (C ∩ D)` is empty and derive a contradiction.
  by_contra hempty
  -- Step 5.1: `Y ∩ C` and `Y ∩ D` are disjoint closed (hence compact) subsets.
  have hYC_closed : IsClosed (Y ∩ C) := hY_closed.inter hC
  have hYD_closed : IsClosed (Y ∩ D) := hY_closed.inter hD
  have hYC_compact : IsCompact (Y ∩ C) := hYC_closed.isCompact
  have hYD_compact : IsCompact (Y ∩ D) := hYD_closed.isCompact
  have hYCD_disj : Disjoint (Y ∩ C) (Y ∩ D) := by
    rw [Set.disjoint_left]
    rintro x ⟨hxY, hxC⟩ ⟨_, hxD⟩
    exact hempty ⟨x, hxY, hxC, hxD⟩
  -- Step 5.2: T2 + compactness gives disjoint open neighborhoods `U ⊇ Y ∩ C`, `V ⊇ Y ∩ D`.
  obtain ⟨U, V, hUopen, hVopen, hYCsubU, hYDsubV, hUVdisj⟩ :=
    SeparatedNhds.of_isCompact_isCompact hYC_compact hYD_compact hYCD_disj
  have hUVopen : IsOpen (U ∪ V) := hUopen.union hVopen
  -- Step 5.3: For every `a ∈ A`, `a \ (U ∪ V)` is nonempty.
  have ha_ne : ∀ a ∈ A, (a \ (U ∪ V)).Nonempty := by
    intro a ha
    by_contra hempty_a
    rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at hempty_a
    -- Step 5.3.1: `a` is preconnected and contained in `U ∪ V` with `U`, `V` disjoint open.
    have hpre := (hConn a ha).isPreconnected
    rcases hpre.subset_or_subset hUopen hVopen hUVdisj hempty_a with haU | haV
    · -- Step 5.3.2a: If `a ⊆ U`, pick `d ∈ Y ∩ D`; then `d ∈ U ∩ V`, contradicting disjointness.
      obtain ⟨d, hdY, hdD⟩ := hDmeet
      have hda : d ∈ a := hY_sub a ha hdY
      exact Set.disjoint_left.mp hUVdisj (haU hda) (hYDsubV ⟨hdY, hdD⟩)
    · -- Step 5.3.2b: Symmetric argument using `Y ∩ C`.
      obtain ⟨c, hcY, hcC⟩ := hCmeet
      have hca : c ∈ a := hY_sub a ha hcY
      exact Set.disjoint_left.mp hUVdisj (hYCsubU ⟨hcY, hcC⟩) (haV hca)
  -- Step 5.4: `{ a \ (U ∪ V) : a ∈ A }` is a directed family of nonempty closed compacts.
  let B : Set (Set X) := (fun a => a \ (U ∪ V)) '' A
  have hB_ne : B.Nonempty := hAne.image _
  have hB_dir : DirectedOn (· ⊇ ·) B := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rcases hChain a b ha hb with hab | hba
    · exact ⟨a \ (U ∪ V), ⟨a, ha, rfl⟩, Set.Subset.refl _,
        Set.diff_subset_diff_left hab⟩
    · exact ⟨b \ (U ∪ V), ⟨b, hb, rfl⟩,
        Set.diff_subset_diff_left hba, Set.Subset.refl _⟩
  have hB_set_ne : ∀ b ∈ B, b.Nonempty := by
    rintro _ ⟨a, ha, rfl⟩; exact ha_ne a ha
  have hB_closed : ∀ b ∈ B, IsClosed b := by
    rintro _ ⟨a, ha, rfl⟩; exact (hClosed a ha).sdiff hUVopen
  have hB_compact : ∀ b ∈ B, IsCompact b := fun b hb => (hB_closed b hb).isCompact
  -- Step 5.5: Cantor again: pick a witness `y ∈ ⋂₀ B`.
  have hY_diff_ne : (⋂₀ B).Nonempty := by
    haveI : Nonempty B := hB_ne.to_subtype
    exact IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
      hB_dir hB_set_ne hB_compact hB_closed
  obtain ⟨y, hy⟩ := hY_diff_ne
  -- Step 5.6: `y` lies in every `a` and avoids `U ∪ V`, so `y ∈ Y \ (U ∪ V)`.
  have hyY : y ∈ Y := by
    intro a ha
    have := hy (a \ (U ∪ V)) ⟨a, ha, rfl⟩
    exact this.1
  have hy_notU : y ∉ U := by
    -- Pick any `a ∈ A`; then `y ∈ a \ (U ∪ V)`, so `y ∉ U`.
    obtain ⟨a, ha⟩ := hAne
    intro hyU
    have := hy (a \ (U ∪ V)) ⟨a, ha, rfl⟩
    exact this.2 (Or.inl hyU)
  have hy_notV : y ∉ V := by
    obtain ⟨a, ha⟩ := hAne
    intro hyV
    have := hy (a \ (U ∪ V)) ⟨a, ha, rfl⟩
    exact this.2 (Or.inr hyV)
  -- Step 5.7: But `Y ⊆ C ∪ D`, and either side forces `y ∈ U` or `y ∈ V`.
  rcases hYsub hyY with hyC | hyD
  · exact hy_notU (hYCsubU ⟨hyY, hyC⟩)
  · exact hy_notV (hYDsubV ⟨hyY, hyD⟩)
