import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Let $p: X \rightarrow Y$ be a closed continuous surjective map such that $p^{-1}(\{y\})$ is compact, for each $y \in Y$. (Such a map is called a perfect map.) Show that if $Y$ is compact, then $X$ is compact.
-/

/-Informal Proof

We first show that if $U$ is an open set containing $p^{-1}(\{y\})$, then there is a neighbourhood $W$ of $y$ such that $p^{-1}(W)$ is contained in $U$. Since $X-U$ is closed in $X$, $p(X-U)$ is closed in $Y$ and does not contain $y$, so $W=Y \backslash p(X \backslash U)$ is a neighbourhood of $y$. Moreover, since $X \backslash U \subset p^{-1}(p(X \backslash U)$ ) (by elementary set theory), we have
$$
p^{-1}(W)=p^{-1}(Y \backslash p(X \backslash U))=p^{-1}(Y) \backslash p^{-1}(p(X \backslash U)) \subset X \backslash(X \backslash U)=U .
$$
Now let $\mathcal{A}$ be an open covering of $X$. For each $y \in Y$, let $\mathcal{A}_y$ be a subcollection of $\mathcal{A}$ such that
$$
p^{-1}(\{y\}) \subset \bigcup_{A \in \mathcal{A}_y} A .
$$
Since $p^{-1}(\{y\})$ is compact, there exists a finite subcollection of $\mathcal{A}_y$ that also covers $p^{-1}(\{y\})$, say $\left\{A_y^1, \ldots, A_y^{n_y}\right\}$. Thus $\bigcup_{i=1}^{n_y} A_y^i$ is open and contains $p^{-1}(\{y\})$, so there exists a neighbourhood $W_y$ of $y$ such that $p^{-1}\left(W_y\right)$ is contained in $\bigcup_{i=1}^{n_y} A_y^i$. Then $\left\{W_y\right\}_{y \in Y}$ is an open covering of $Y$, so there exist $y_1, \ldots, y_k \in Y$ such that $\left\{W_{y_j}\right\}_{j=1}^k$ also covers $Y$. Then
$$
X=p^{-1}(Y) \subset p^{-1}\left(\bigcup_{j=1}^k W_{y_j}\right)=\bigcup_{j=1}^k p^{-1}\left(W_{y_j}\right) \subset \bigcup_{j=1}^k\left(\bigcup_{i=1}^{n_{y_j}} A_{y_j}^i\right)
$$
so
$$
\left\{A_{y_j}^i\right\}_{\substack{j=1, \ldots, k . \\ i=1, \ldots, n_{y_j}}}
$$
is a finite subcollection of $\mathcal{A}$ that also covers $X$. Therefore, $X$ is compact.
-/

theorem Munkres_exercise_26_12 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (p : X → Y) (_h : Function.Surjective p) (_hc : Continuous p)
  (hp : IsClosedMap p) (hp : ∀ y, IsCompact (p ⁻¹' {y}))
  (hY : CompactSpace Y) : CompactSpace X := by
  classical
  -- Step 1: Rename the two hypotheses both called `hp` so that the closed-map
  --         information and the fibre-compactness information are simultaneously usable.
  revert hp
  revert hp
  intro hClosedMap hFiberCompact
  -- Step 2: Reduce compactness of `X` to the finite subcover formulation for the
  --         open cover of `Set.univ`.
  refine ⟨?_⟩
  refine (isCompact_iff_finite_subcover).2 ?_
  intro ι U hUopen hcover
  -- Step 3: For each fibre `p ⁻¹' {y}` pick a finite subcollection of the open
  --         cover that still covers that fibre.
  have hFiberData :
      ∀ y : Y, ∃ t : Finset ι, p ⁻¹' ({y} : Set Y) ⊆ ⋃ i ∈ t, U i := by
    intro y
    -- Step 3.1: Because the cover hits every point of `X`, it certainly covers
    --           each compact fibre.
    have hcoverFiber : p ⁻¹' ({y} : Set Y) ⊆ ⋃ i, U i := by
      intro x hx
      -- Step 3.1.1: Membership in `p ⁻¹' {y}` entails membership in `Set.univ`.
      have hxuniv : x ∈ (Set.univ : Set X) := trivial
      exact hcover hxuniv
    -- Step 3.2: Apply compactness of the fibre to extract the promised finite
    --           subcover.
    obtain ⟨t, ht⟩ :=
      (hFiberCompact y).elim_finite_subcover (U := U) (fun i => hUopen i) hcoverFiber
    exact ⟨t, ht⟩
  -- Step 4: Use classical choice to assign to each `y` both the finite index set
  --         and the resulting finite union.
  choose t ht using hFiberData
  -- Step 4.1: Each of these finite unions is open, so their complements are
  --           closed, a fact needed for the closed-map argument.
  have hUnionOpen : ∀ y : Y, IsOpen (⋃ i ∈ t y, U i) := by
    intro y
    refine isOpen_iUnion ?_
    intro i
    refine isOpen_iUnion ?_
    intro _
    simpa using hUopen i
  -- Step 4.2: Define the closed complements in `X` and the induced neighbourhoods
  --           `W y` in `Y`.
  let C : Y → Set X := fun y => (⋃ i ∈ t y, U i)ᶜ
  let W : Y → Set Y := fun y => (p '' C y)ᶜ
  -- Step 4.3: By the closed-map property, every `W y` is open.
  have hWopen : ∀ y : Y, IsOpen (W y) := by
    intro y
    have hCclosed : IsClosed (C y) := by
      simpa [C] using (hUnionOpen y).isClosed_compl
    have hImageClosed : IsClosed (p '' C y) := hClosedMap _ hCclosed
    simpa [W] using hImageClosed.isOpen_compl
  -- Step 4.4: Each `y` actually lies inside its neighbourhood `W y` because the
  --           fibre over `y` never meets the closed set `C y`.
  have hyW : ∀ y : Y, y ∈ W y := by
    intro y
    have hyNot : y ∉ p '' C y := by
      rintro ⟨x, hxC, hpx⟩
      have hxFiber : x ∈ p ⁻¹' ({y} : Set Y) := by
        change p x ∈ ({y} : Set Y)
        simp [Set.mem_singleton_iff, hpx]
      have hxUnion : x ∈ ⋃ i ∈ t y, U i := ht y hxFiber
      have : x ∉ ⋃ i ∈ t y, U i := by
        simpa [C] using hxC
      exact this hxUnion
    simpa [W] using hyNot
  -- Step 4.5: Pulling back each `W y` along `p` lands inside the chosen finite
  --           union because otherwise the closed set `C y` would map onto `W y`.
  have hWpreimage_subset :
      ∀ y : Y, p ⁻¹' (W y) ⊆ ⋃ i ∈ t y, U i := by
    intro y x hx
    classical
    by_contra hxnot
    have hxC : x ∈ C y := by simpa [C] using hxnot
    have hpx : p x ∉ p '' C y := by
      simpa [Set.mem_preimage, W] using hx
    exact hpx ⟨x, hxC, rfl⟩
  -- Step 5: Use compactness of `Y` to select finitely many neighbourhoods `W y`
  --         that already cover `Y`.
  have hYcover : (Set.univ : Set Y) ⊆ ⋃ y : Y, W y := by
    intro y _
    refine Set.mem_iUnion.2 ?_
    exact ⟨y, hyW y⟩
  have hYcompact : IsCompact (Set.univ : Set Y) := isCompact_univ
  obtain ⟨s, hscov⟩ :=
    hYcompact.elim_finite_subcover (U := fun y : Y => W y) (fun y => hWopen y) hYcover
  -- Step 6: Pull the finite cover of `Y` back along `p`, giving a finite family of
  --         unions that still covers all of `X`.
  have hcoverX :
      (Set.univ : Set X) ⊆ ⋃ y ∈ s, ⋃ i ∈ t y, U i := by
    intro x hx
    have hpx : p x ∈ (Set.univ : Set Y) := trivial
    have hpxCov : p x ∈ ⋃ y ∈ s, W y := hscov hpx
    rcases Set.mem_iUnion.1 hpxCov with ⟨y, hy⟩
    rcases Set.mem_iUnion.1 hy with ⟨hy_s, hpWy⟩
    have hxpre : x ∈ p ⁻¹' (W y) := by
      simpa [Set.mem_preimage] using hpWy
    have hxUnion : x ∈ ⋃ i ∈ t y, U i := hWpreimage_subset y hxpre
    refine Set.mem_iUnion.2 ?_
    exact ⟨y, Set.mem_iUnion.2 ⟨hy_s, hxUnion⟩⟩
  -- Step 7: Flatten the doubly indexed finite collection into a single finite
  --         subset of indices of the original cover.
  let T : Finset ι := s.biUnion fun y => t y
  have hsubsetUnion :
      (⋃ y ∈ s, ⋃ i ∈ t y, U i) ⊆ ⋃ i ∈ T, U i := by
    intro x hx
    classical
    rcases Set.mem_iUnion.1 hx with ⟨y, hy⟩
    rcases Set.mem_iUnion.1 hy with ⟨hy_s, hxmem⟩
    rcases Set.mem_iUnion.1 hxmem with ⟨i, hi⟩
    rcases Set.mem_iUnion.1 hi with ⟨hi_ty, hxU⟩
    refine Set.mem_iUnion.2 ?_
    have hiT : i ∈ T := by
      refine (Finset.mem_biUnion.2 ?_)
      exact ⟨y, hy_s, hi_ty⟩
    exact ⟨i, Set.mem_iUnion.2 ⟨hiT, hxU⟩⟩
  refine ⟨T, ?_⟩
  exact Set.Subset.trans hcoverX hsubsetUnion
