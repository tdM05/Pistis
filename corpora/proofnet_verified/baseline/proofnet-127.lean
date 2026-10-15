import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Show that if $X$ is a Hausdorff space that is locally compact at the point $x$, then for each neighborhood $U$ of $x$, there is a neighborhood $V$ of $x$ such that $\bar{V}$ is compact and $\bar{V} \subset U$.
-/

/-Informal Proof

Let $U$ be a neighbourhood of $x$. Since $X$ is locally compact at $x$, there exists a compact subspace $C$ of $X$ containing a neighbourhood $W$ of $x$. Then $U \cap W$ is open in $X$, hence in $C$. Thus, $C \backslash(U \cap W)$ is closed in $C$, hence compact. Since $X$ is Hausdorff, there exist disjoint open sets $V_1$ and $V_2$ of $X$ containing $x$ and $C \backslash(U \cap W)$ respectively. Let $V=V_1 \cap U \cap W$. Since $\bar{V}$ is closed in $C$, it is compact. Furthermore, $\bar{V}$ is disjoint from $C \backslash(U \cap W) \supset C \backslash U$, so $\bar{V} \subset U$.
-/

theorem Munkres_exercise_29_10 {X : Type*}
  [TopologicalSpace X] [T2Space X] (x : X)
  (hx : ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ (∃ K : Set X, U ⊆ K ∧ IsCompact K))
  (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) :
  ∃ (V : Set X), IsOpen V ∧ x ∈ V ∧ IsCompact (closure V) ∧ closure V ⊆ U := by
  classical
  -- Step 1: Unpack the local compactness data around x into a convenient compact neighbourhood.
  obtain ⟨N, hxN, hNopen, ⟨K, hNsubsetK, hKcompact⟩⟩ := hx
  -- Step 1.1: Register that x lies inside the compact set K and that K is closed in the Hausdorff space.
  have hxK : x ∈ K := hNsubsetK hxN
  have hKclosed : IsClosed K := hKcompact.isClosed
  -- Step 1.2: Record that the part of K outside U is compact and that x does not belong to it.
  set KminusU := K \ U
  have hKminusU_compact : IsCompact KminusU := hKcompact.diff hU
  -- Step 2: For every point y in K \ U, separate it from x by disjoint open sets.
  have hSeparation :
      ∀ y : {y : X // y ∈ KminusU},
        ∃ (Vy Oy : Set X),
          IsOpen Vy ∧ IsOpen Oy ∧ x ∈ Vy ∧ (y : X) ∈ Oy ∧ Disjoint Vy Oy := by
    intro y
    -- Step 2.1: Extract the useful membership facts for the chosen y.
    rcases y.property with ⟨_, hy_notU⟩
    -- Step 2.2: Use the Hausdorff property to get disjoint neighbourhoods of x and y.
    have hne : x ≠ (y : X) := by
      intro hxy
      exact hy_notU (by simpa [hxy] using hxU)
    obtain ⟨Vy, Oy, hVyOpen, hOyOpen, hxVy, hyOy, hDisjoint⟩ := t2_separation hne
    -- Step 2.3: Package the separation data for later use.
    exact ⟨Vy, Oy, hVyOpen, hOyOpen, hxVy, hyOy, hDisjoint⟩
  -- Step 3: Choose concrete functions assigning each y suitable separating open sets.
  choose Vfun Ofun hVfun_open hOfun_open hxVfun hyOfun hDisjoint using hSeparation
  -- Step 4: Apply compactness of K \ U to extract finitely many of those open sets covering it.
  obtain ⟨t, hCover_t⟩ :=
    hKminusU_compact.elim_finite_subcover
      (fun y : {y : X // y ∈ KminusU} => Ofun y)
      (fun y => hOfun_open y)
      (by
        -- Step 4.1: Show that every point of K \ U lies in the corresponding chosen open set.
        intro z hz
        refine mem_iUnion.2 ?_
        refine ⟨⟨z, hz⟩, ?_⟩
        simpa using hyOfun ⟨z, hz⟩)
  -- Step 5: Intersect the finitely many open neighbourhoods of x obtained above.
  set V0 : Set X := ⋂ y ∈ t, Vfun y
  -- Step 5.1: Prove that this finite intersection is open.
  have hV0_open : IsOpen V0 := by
    -- Step 5.1.1: Apply the finite-intersection lemma for open sets.
    classical
    unfold V0
    simpa using
      (isOpen_biInter_finset (s := t) (f := fun y => Vfun y)
        (fun y hy => hVfun_open y))
  -- Step 5.2: Note that x lies in the intersection of all these neighbourhoods.
  have hx_V0 : x ∈ V0 := by
    classical
    refine mem_iInter₂.mpr ?_
    intro y hy
    -- Step 5.2.1: Since x lies in every Vfun y, it also lies in their intersection.
    simpa using hxVfun y
  -- Step 6: Build the candidate open set V by intersecting V0 with the original open neighbourhood N.
  set V : Set X := V0 ∩ N
  -- Step 6.1: V is open because it is the intersection of two open sets.
  have hV_open : IsOpen V := hV0_open.inter hNopen
  -- Step 6.2: x belongs to V because it belongs to both V0 and N.
  have hxV : x ∈ V := ⟨hx_V0, hxN⟩
  -- Step 6.3: V is contained in the compact set K.
  have hV_subset_K : V ⊆ K := by
    intro z hz
    exact hNsubsetK hz.2
  -- Step 7: Leverage closure properties to keep track of where closure V can live.
  have hClosure_subset_K : closure V ⊆ K :=
    closure_minimal hV_subset_K hKclosed
  -- Step 7.1: Points in closure V cannot enter any Ofun y, otherwise they would contradict the closure property.
  have hClosure_subset_compl :
      closure V ⊆ (⋃ y ∈ t, Ofun y)ᶜ := by
    intro z hz
    classical
    -- Step 7.1.1: Suppose, towards contradiction, that z lies in some Ofun y.
    by_contra hz_mem
    have hz_mem_union : z ∈ ⋃ y ∈ t, Ofun y := by
      classical
      simpa [Set.mem_compl] using hz_mem
    obtain ⟨y, hy_mem, hz_in_Ofun⟩ := mem_iUnion₂.1 hz_mem_union
    have hOfun_nhds : Ofun y ∈ 𝓝 z := (hOfun_open y).mem_nhds hz_in_Ofun
    have hInter_nonempty :=
      mem_closure_iff_nhds.1 hz (Ofun y) hOfun_nhds
    -- Step 7.1.2: Use the disjointness obtained earlier to forbid such an intersection.
    rcases hInter_nonempty with ⟨w, hw_inter⟩
    rcases hw_inter with ⟨hwOfun, hwV⟩
    exact
      (Set.disjoint_left.mp (hDisjoint y))
        (mem_iInter₂.mp hwV.1 y hy_mem) hwOfun
  -- Step 7.2: Combine the previous bounds to see that closure V lives inside U.
  have hSubset_to_U : K ∩ (⋃ y ∈ t, Ofun y)ᶜ ⊆ U := by
    intro z hz
    classical
    have hzK : z ∈ K := hz.1
    have hz_not_union : z ∉ ⋃ y ∈ t, Ofun y := by
      simpa [Set.mem_compl] using hz.2
    by_contra hz_notU
    have hz_in_KminusU : z ∈ KminusU := ⟨hzK, hz_notU⟩
    have hz_in_union : z ∈ ⋃ y ∈ t, Ofun y := hCover_t hz_in_KminusU
    exact hz_not_union hz_in_union
  have hClosure_subset_U : closure V ⊆ U := by
    intro z hz
    have hzK : z ∈ K := hClosure_subset_K hz
    have hz_not_union : z ∈ (⋃ y ∈ t, Ofun y)ᶜ := hClosure_subset_compl hz
    exact hSubset_to_U ⟨hzK, hz_not_union⟩
  -- Step 8: The closure of V is a closed subset of the compact set K, hence compact.
  have hClosure_compact : IsCompact (closure V) :=
    hKcompact.of_isClosed_subset isClosed_closure hClosure_subset_K
  -- Step 9: Conclude by gathering all ingredients for the desired neighbourhood V.
  refine ⟨V, hV_open, hxV, hClosure_compact, hClosure_subset_U⟩
