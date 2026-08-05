import Mathlib

open Filter Set TopologicalSpace Topology



/-Informal Statement

Let $p: X \rightarrow Y$ be a quotient map. Show that if each set $p^{-1}(\{y\})$ is connected, and if $Y$ is connected, then $X$ is connected.
-/

/-Informal Proof

Suppose that $U$ and $V$ constitute a separation of $X$. If $y \in p(U)$, then $y=p(x)$ for some $x \in U$, so that $x \in p^{-1}(\{y\})$. Since $p^{-1}(\{y\})$ is connected and $x \in U \cap p^{-1}(\{y\})$, we have $p^{-1}(\{y\}) \subset U$. Thus $p^{-1}(\{y\}) \subset U$ for all $y \in p(U)$, so that $p^{-1}(p(U)) \subset U$. The inclusion $U \subset p^{-1}(p(U))$ if true for any subset and function, so we have the equality $U=p^{-1}(p(U))$ and therefore $U$ is saturated. Similarly, $V$ is saturated. Since $p$ is a quotient map, $p(U)$ and $p(V)$ are disjoint non-empty open sets in $Y$. But $p(U) \cup p(V)=Y$ as $p$ is surjective, so $p(U)$ and $p(V)$ constitute a separation of $Y$, contradicting the fact that $Y$ is connected. We conclude that $X$ is connected.
-/

theorem Munkres_exercise_23_11 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (p : X → Y) (hq : IsQuotientMap p)
  (hY : ConnectedSpace Y) (hX : ∀ y : Y, IsConnected (p ⁻¹' {y})) :
  ConnectedSpace X := by
  classical
  -- Step 1: Translate the connectedness of `Y` to `IsConnected (Set.univ : Set Y)`.
  have hYconn : IsConnected (Set.univ : Set Y) := (connectedSpace_iff_univ.mp hY)
  -- Step 1.1: Pick a base point of `Y` and lift it along the surjective quotient map.
  obtain ⟨y₀, -⟩ := hYconn.1
  obtain ⟨x₀, _⟩ := hq.surjective y₀
  -- Step 1.2: Package the lifted point as evidence that `X` is nonempty.
  have hXnonempty : (Set.univ : Set X).Nonempty := ⟨x₀, by simp⟩
  -- Step 1.3: Reduce the goal to the connectivity of `Set.univ`.
  refine connectedSpace_iff_univ.mpr ?_
  -- Step 2: It suffices to show that `Set.univ : Set X` is connected.
  refine ⟨hXnonempty, ?_⟩
  -- Step 3: Prove preconnectedness; fix an arbitrary open cover by `U` and `V`.
  intro U V hUopen hVopen hcover hUN hVN
  -- Step 3.1: Record that both open sets are nonempty.
  have hUN' : U.Nonempty := by simpa [Set.univ_inter] using hUN
  have hVN' : V.Nonempty := by simpa [Set.univ_inter, Set.inter_comm] using hVN
  -- Step 3.2: For convenience, rewrite the cover condition pointwise.
  have hcover' : ∀ z : X, z ∈ U ∪ V := fun z => by
    simpa using hcover (by simp : z ∈ (Set.univ : Set X))
  -- Step 3.3: Assume towards contradiction that the two opens have empty intersection.
  by_contra h_inter
  have h_inter' : ¬ (U ∩ V).Nonempty := by
    simpa [Set.inter_assoc, Set.inter_left_comm, Set.univ_inter, Set.inter_univ] using h_inter
  -- Step 3.4: Deduce that `U` and `V` are disjoint.
  have hdisjUV : Disjoint U V := by
    refine disjoint_left.mpr ?_
    intro x hxU hxV
    exact h_inter' ⟨x, ⟨hxU, hxV⟩⟩
  -- Step 3.5: Fibers above points of `p '' U` remain in `U`.
  have hFiber_subset_of_memU :
      ∀ ⦃y : Y⦄, y ∈ p '' U → p ⁻¹' ({y} : Set Y) ⊆ U := by
    intro y hy
    rcases hy with ⟨xU, hxU, rfl⟩
    intro z hz
    by_contra hzU
    have hzV : z ∈ V := by
      rcases hcover' z with h | h
      · exact (hzU h).elim
      · exact h
    have hFiber := hX (p xU)
    have hFiberSubsetUnion :
        p ⁻¹' ({p xU} : Set Y) ⊆ U ∪ V := by
      intro w _
      rcases hcover' w with hw | hw
      · exact Or.inl hw
      · exact Or.inr hw
    have hFiberU :
        (p ⁻¹' ({p xU} : Set Y) ∩ U).Nonempty :=
      ⟨xU, by
        refine ⟨?_, hxU⟩
        simp⟩
    have hFiberV :
        (p ⁻¹' ({p xU} : Set Y) ∩ V).Nonempty :=
      ⟨z, ⟨hz, hzV⟩⟩
    obtain ⟨w, -, hwUV⟩ :=
        (hFiber.2) U V hUopen hVopen hFiberSubsetUnion hFiberU hFiberV
    exact h_inter' ⟨w, hwUV⟩
  -- Step 3.6: Apply the same reasoning to fibers above points of `p '' V`.
  have hFiber_subset_of_memV :
      ∀ ⦃y : Y⦄, y ∈ p '' V → p ⁻¹' ({y} : Set Y) ⊆ V := by
    intro y hy
    rcases hy with ⟨xV, hxV, rfl⟩
    intro z hz
    by_contra hzV
    have hzU : z ∈ U := by
      rcases hcover' z with h | h
      · exact h
      · exact (hzV h).elim
    have hFiber := hX (p xV)
    have hFiberSubsetUnion :
        p ⁻¹' ({p xV} : Set Y) ⊆ U ∪ V := by
      intro w _
      rcases hcover' w with hw | hw
      · exact Or.inl hw
      · exact Or.inr hw
    have hFiberU :
        (p ⁻¹' ({p xV} : Set Y) ∩ U).Nonempty :=
      ⟨z, ⟨hz, hzU⟩⟩
    have hFiberV :
        (p ⁻¹' ({p xV} : Set Y) ∩ V).Nonempty :=
      ⟨xV, by
        refine ⟨?_, hxV⟩
        simp⟩
    obtain ⟨w, -, hwUV⟩ :=
        (hFiber.2) U V hUopen hVopen hFiberSubsetUnion hFiberU hFiberV
    exact h_inter' ⟨w, hwUV⟩
  -- Step 3.7: Conclude that `U` and `V` are saturated with respect to `p`.
  have hUSat : U = p ⁻¹' (p '' U) := by
    refine Set.Subset.antisymm ?_ ?_
    · intro x hxU
      change p x ∈ p '' U
      exact ⟨x, hxU, rfl⟩
    · intro x hx
      have hx' : p x ∈ p '' U := by
        simpa [Set.mem_preimage] using hx
      have hxFiber : x ∈ p ⁻¹' ({p x} : Set Y) := by
        change p x ∈ ({p x} : Set Y)
        simp
      have hxSubset := hFiber_subset_of_memU hx'
      simpa using hxSubset hxFiber
  have hVSat : V = p ⁻¹' (p '' V) := by
    refine Set.Subset.antisymm ?_ ?_
    · intro x hxV
      change p x ∈ p '' V
      exact ⟨x, hxV, rfl⟩
    · intro x hx
      have hx' : p x ∈ p '' V := by
        simpa [Set.mem_preimage] using hx
      have hxFiber : x ∈ p ⁻¹' ({p x} : Set Y) := by
        change p x ∈ ({p x} : Set Y)
        simp
      have hxSubset := hFiber_subset_of_memV hx'
      simpa using hxSubset hxFiber
  -- Step 3.8: Use the quotient condition to deduce that the images of `U` and `V` are open.
  have hPreimageOpenU : IsOpen (p ⁻¹' (p '' U)) := by
    simpa [hUSat.symm] using hUopen
  have hPreimageOpenV : IsOpen (p ⁻¹' (p '' V)) := by
    simpa [hVSat.symm] using hVopen
  have hOpenImageU : IsOpen (p '' U) :=
    (hq.isOpen_preimage).mp hPreimageOpenU
  have hOpenImageV : IsOpen (p '' V) :=
    (hq.isOpen_preimage).mp hPreimageOpenV
  -- Step 3.9: Note that the images are nonempty because the original opens are.
  have hImageUNonempty : (p '' U).Nonempty := by
    rcases hUN' with ⟨x, hx⟩
    exact ⟨p x, ⟨x, hx, rfl⟩⟩
  have hImageVNonempty : (p '' V).Nonempty := by
    rcases hVN' with ⟨x, hx⟩
    exact ⟨p x, ⟨x, hx, rfl⟩⟩
  -- Step 3.10: Show that the images still cover `Y` because `p` is surjective.
  have hImageCover : (Set.univ : Set Y) ⊆ p '' U ∪ p '' V := by
    intro y _
    rcases hq.surjective y with ⟨x, rfl⟩
    rcases hcover' x with hx | hx
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  -- Step 3.11: Prove that the two images are disjoint, still using fiberwise connectedness.
  have hImageDisjoint : Disjoint (p '' U) (p '' V) := by
    refine disjoint_left.mpr ?_
    intro y hyU hyV
    rcases hyU with ⟨xU, hxU, hpxU⟩
    rcases hyV with ⟨xV, hxV, hpxV⟩
    have hFiber := hX y
    have hxUfiber : xU ∈ p ⁻¹' ({y} : Set Y) := by
      simp [Set.mem_preimage, hpxU]
    have hxVfiber : xV ∈ p ⁻¹' ({y} : Set Y) := by
      simp [Set.mem_preimage, hpxV]
    have hFiberSubsetUnion :
        p ⁻¹' ({y} : Set Y) ⊆ U ∪ V := by
      intro w _
      rcases hcover' w with hw | hw
      · exact Or.inl hw
      · exact Or.inr hw
    have hFiberU :
        (p ⁻¹' ({y} : Set Y) ∩ U).Nonempty :=
      ⟨xU, ⟨hxUfiber, hxU⟩⟩
    have hFiberV :
        (p ⁻¹' ({y} : Set Y) ∩ V).Nonempty :=
      ⟨xV, ⟨hxVfiber, hxV⟩⟩
    obtain ⟨w, -, hwUV⟩ :=
        (hFiber.2) U V hUopen hVopen hFiberSubsetUnion hFiberU hFiberV
    exact h_inter' ⟨w, hwUV⟩
  -- Step 3.12: Apply the connectedness of `Y` to the images and obtain a contradiction.
  have hYpre := hYconn.2
  have hImageInter :
      ((Set.univ : Set Y) ∩ ((p '' U) ∩ (p '' V))).Nonempty :=
    hYpre (p '' U) (p '' V) hOpenImageU hOpenImageV hImageCover
      (by simpa [Set.univ_inter] using hImageUNonempty)
      (by simpa [Set.univ_inter] using hImageVNonempty)
  have : (p '' U ∩ p '' V).Nonempty := by
    simpa [Set.inter_assoc, Set.univ_inter, Set.inter_univ] using hImageInter
  rcases this with ⟨y, hyU, hyV⟩
  exact (disjoint_left.mp hImageDisjoint) hyU hyV
