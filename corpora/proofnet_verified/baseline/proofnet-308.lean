import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

def countably_compact (X : Type*) [TopologicalSpace X] :=
  ∀ U : ℕ → Set X,
  (∀ i, IsOpen (U i)) ∧ ((univ : Set X) ⊆ ⋃ i, U i) →
  (∃ t : Finset ℕ, (univ : Set X) ⊆ ⋃ i ∈ t, U i)

def limit_point_compact (X : Type*) [TopologicalSpace X] :=
  ∀ U : Set X, Infinite U → ∃ x ∈ U, ClusterPt x (𝓟 U)

/-Informal Statement

A space $X$ is said to be countably compact if every countable open covering of $X$ contains a finite subcollection that covers $X$. Show that for a $T_1$ space $X$, countable compactness is equivalent to limit point compactness.
-/

/-Informal Proof

First let $X$ be a countable compact space. Note that if $Y$ is a closed subset of $X$, then $Y$ is countable compact as well, for if $\left\{U_n\right\}_{n \in \mathbb{Z}_{+}}$is a countable open covering of $Y$, then $\left\{U_n\right\}_{n \in \mathbb{Z}_{+}} \cup(X \backslash Y)$ is a countable open covering of $X$; there is a finite subcovering of $X$, hence a finite subcovering of $Y$. Now let $A$ be an infinite subset. We show that $A$ has a limit point. Let $B$ be a countable infinite subset of $A$. Suppose that $B$ has no limit point, so that $B$ is closed in $X$. Then $B$ is countable compact. Since $B$ has no limit point, for each $b \in B$ there is a neighbourhood $U_b$ of $b$ that intersects $B$ in the point $b$ alone. Then $\left\{U_b\right\}_{b \in B}$ is an open covering of $B$ with no finite subcovering, contradicting the fact that $B$ is countable compact. Hence $B$ has a limit point, so that $A$ has a limit point as well. Since $A$ was arbitrary, we deduce that $X$ is limit point compact. (Note that the $T_1$ property is not necessary in this direction.)

Now assume that $X$ is a limit point compact $T_1$ space. We show that $X$ is countable compact. Suppose, on the contrary, that $\left\{U_n\right\}_{n \in \mathbb{Z}_{+}}$is a countable open covering of $X$ with no finite subcovering. For each $n$, take a point $x_n$ in $X$ not in $U_1 \cup \cdots \cup U_n$. By assumption, the infinite set $A=\left\{x_n \mid n \in \mathbb{Z}_{+}\right\}$has a limit point $y \in X$. Since $\left\{U_n\right\}_{n \in \mathbb{Z}_{+}}$covers $X$, there exists $N \in \mathbb{Z}_{+}$such that $y \in U_1 \cup \cdots \cup U_N$. Now $X$ is $T_1$, so for each $i=1, \ldots, N$ there exists a neighbourhood $V_i$ of $y$ that does not contain $x_i$. Then
$$
V=\left(V_1 \cap \cdots \cap V_N\right) \cap\left(U_1 \cup \cdots \cup U_N\right)
$$
is a neighbourhood of $y$ that does not contain any of the points $x_i$, contradicting the fact that $y$ is a limit point of $A$. It follows that every countable open covering of $X$ must have a finite subcovering, so $X$ is countable compact.
-/

theorem Munkres_exercise_28_4 {X : Type*}
  [TopologicalSpace X] (hT1 : T1Space X) :
  countably_compact X ↔ limit_point_compact X := by
  sorry

/-!
######################################################################
# Why the formal statement above is false as written
######################################################################
-/

open scoped Classical

-- Step 1: A point belonging to a set is automatically a cluster point
--         for the principal filter of that set.
lemma clusterPt_principal_of_mem {X : Type*} [TopologicalSpace X]
    {U : Set X} {x : X} (hx : x ∈ U) : ClusterPt x (𝓟 U) := by
  refine (clusterPt_iff_nonempty).2 ?_
  intro V hV V' hV'
  have hsub : U ⊆ V' := hV'
  have hxV' : x ∈ V' := hsub hx
  have hxV : x ∈ V := by
    have : x ∈ interior V := (mem_interior_iff_mem_nhds).2 hV
    exact interior_subset this
  exact ⟨x, hxV, hxV'⟩

-- Step 2: With that lemma, every space satisfies the given
--         `limit_point_compact` predicate.
lemma limit_point_compact_trivial (X : Type*) [TopologicalSpace X] :
    limit_point_compact X := by
  intro U hInf
  classical
  -- obtain a point of the infinite subtype via an embedding of ℕ
  let e : ℕ ↪ U := Infinite.natEmbedding _
  let x : X := (e 0).1
  have hx : x ∈ U := (e 0).property
  exact ⟨x, hx, clusterPt_principal_of_mem hx⟩

-- Step 3: The discrete space of naturals is not countably compact.
lemma not_countably_compact_nat : ¬ countably_compact ℕ := by
  classical
  let U : ℕ → Set ℕ := fun n => {n}
  have hOpen : ∀ n, IsOpen (U n) := fun n => by simp [U]
  have hCover : (Set.univ : Set ℕ) ⊆ ⋃ n, U n := by
    intro x _; refine Set.mem_iUnion.2 ⟨x, by simp [U]⟩
  intro hcc
  obtain ⟨t, ht⟩ := hcc U ⟨hOpen, hCover⟩
  have hUnion : (⋃ i ∈ t, U i) = (t : Set ℕ) := by
    ext x; constructor
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
      rcases Set.mem_iUnion.1 hi with ⟨hi_t, hx'⟩
      have hxEq : x = i := by simpa [U] using hx'
      subst hxEq; simpa using hi_t
    · intro hx; refine Set.mem_iUnion.2 ?_
      exact ⟨x, Set.mem_iUnion.2 ⟨by simpa using hx, by simp [U]⟩⟩
  have hsubset : (Set.univ : Set ℕ) ⊆ (t : Set ℕ) := by simpa [hUnion] using ht
  have hfinite : (Set.univ : Set ℕ).Finite := (t.finite_toSet).subset hsubset
  have hinf : (Set.univ : Set ℕ).Infinite := Set.infinite_univ
  exact hfinite.not_infinite hinf

-- Step 4: Combine the previous lemmas to refute the formal equivalence.
theorem Munkres_exercise_28_4_neg :
    ¬ (countably_compact ℕ ↔ limit_point_compact ℕ) := by
  intro h
  have hL : limit_point_compact ℕ := limit_point_compact_trivial ℕ
  have hcc : countably_compact ℕ := (h).mpr hL
  exact not_countably_compact_nat hcc

/-!
######################################################################
# A corrected formulation
######################################################################

To exclude the trivial cluster points, require neighbourhoods to meet
the punctured set.  This “strong” variant captures the intended
accumulation-point notion.
-/

def limit_point_compact_strong (X : Type*) [TopologicalSpace X] :=
  ∀ U : Set X, Infinite U → ∃ x, ClusterPt x (𝓟 (U \ {x}))


theorem Munkres_exercise_28_4_corrected {X : Type*} [TopologicalSpace X]
    (hT1 : T1Space X) : countably_compact X ↔ limit_point_compact_strong X := by
  constructor
  · -- Forward direction: countably compact → limit point compact (strong).
    classical
    intro hcc U hInf
    -- Step 1: Argue by contradiction: assume no point clusters `U \ {x}`.
    by_contra hNoCluster
    -- Step 1.1: Rephrase the negated goal pointwise for easy access.
    have hNoCluster' : ∀ x : X, ¬ ClusterPt x (𝓟 (U \ {x})) :=
      not_exists.mp hNoCluster
    -- Step 1.2: Install the infinitude of `U` as an instance for typeclass tools.
    haveI : Infinite U := hInf
    -- Step 2: Choose a countably infinite sequence inside `U` to build
    --         the contradictory open cover.
    let e : ℕ ↪ U := Infinite.natEmbedding U
    let b : ℕ → X := fun n => (e n).1
    -- Step 2.1: Every sampled point really lies in `U`.
    have hb_mem : ∀ n, b n ∈ U := fun n => (e n).2
    -- Step 2.2: The enumeration is injective (crucial to keep points distinct).
    have hb_inj : Function.Injective b := by
      intro n m h
      apply e.injective
      apply Subtype.ext
      simpa [b] using h
    -- Step 2.3: Record the sampled subset as a set `B`.
    let B : Set X := Set.range b
    -- Step 2.4: `B` is infinite because it is the range of an injective map from ℕ.
    have hB_inf : B.Infinite := by
      have : (Set.range b).Infinite := Set.infinite_range_of_injective hb_inj
      simpa [B] using this
    -- Step 3: Show `B` is closed using the assumption that no point clusters `U \ {x}`.
    have hB_closed : IsClosed B := by
      -- Step 3.1: Any cluster point of `B` must actually be in `B`, otherwise
      --           it would contradict the global “no cluster” assumption.
      refine (isClosed_iff_clusterPt).2 ?_
      intro x hxClusterB
      -- Step 3.2: If `x ∉ B`, then `B ⊆ U \ {x}` and clustering `B` forces
      --           clustering `U \ {x}`.
      by_contra hxNotIn
      have hSub : B ⊆ U \ {x} := by
        intro y hyB
        rcases hyB with ⟨n, rfl⟩
        refine ⟨hb_mem n, ?_⟩
        -- Step 3.3: `x ∉ B` guarantees each `b n` is different from `x`.
        have hNe : b n ≠ x := by
          intro hEq
          subst hEq
          exact hxNotIn ⟨n, rfl⟩
        simpa [Set.mem_singleton_iff] using hNe
      have hxClusterU : ClusterPt x (𝓟 (U \ {x})) :=
        hxClusterB.mono (principal_mono.2 hSub)
      exact hNoCluster' x hxClusterU
    -- Step 4: For each `b n`, build an open neighbourhood meeting `U` only in `b n`.
    let V : ℕ → Set X := fun n => (closure (U \ {b n}))ᶜ
    -- Step 4.1: Each `V n` is open by construction.
    have hV_open : ∀ n, IsOpen (V n) := fun _ => isClosed_closure.isOpen_compl
    -- Step 4.2: Each `b n` belongs to `V n` because it is not a cluster point of `U \ {b n}`.
    have hb_in_V : ∀ n, b n ∈ V n := by
      intro n
      have hNotCluster := hNoCluster' (b n)
      have hNotClosure : b n ∉ closure (U \ {b n}) := by
        -- Step 4.2.1: Using `mem_closure_iff_clusterPt` to flip between clustering and closure.
        simpa [mem_closure_iff_clusterPt] using hNotCluster
      -- Step 4.2.2: Membership in the complement is exactly the negated closure membership.
      simpa [V] using hNotClosure
    -- Step 4.3: Intersecting `V n` with `U` leaves only the point `b n`.
    have hV_inter_singleton : ∀ n, V n ∩ U ⊆ ({b n} : Set X) := by
      intro n x hx
      rcases hx with ⟨hxV, hxU⟩
      -- Step 4.3.1: Points of `U` lying in `V n` cannot be different from `b n`, otherwise
      --             they would belong to `U \ {b n}` contradicting the disjointness with `V n`.
      by_cases hEq : x = b n
      · simp [hEq]
      · have hxClosure : x ∈ closure (U \ {b n}) :=
          subset_closure ⟨hxU, by simp [Set.mem_singleton_iff, hEq]⟩
        have hxCompl : x ∉ closure (U \ {b n}) := by
          have : x ∈ V n := hxV
          simpa [V] using this
        -- Step 4.3.2: Disjointness forces a contradiction; hence only `b n` survives.
        exact (hxCompl hxClosure).elim
    -- Step 4.4: No other sampled point sneaks into `V n`.
    have hV_hits_only : ∀ {n m}, b m ∈ V n → n = m := by
      intro n m hbmV
      have hInU : b m ∈ U := hb_mem m
      have hInSingleton : b m ∈ ({b n} : Set X) := hV_inter_singleton n ⟨hbmV, hInU⟩
      have hEq : b m = b n := by simpa using hInSingleton
      have hm : m = n := hb_inj hEq
      simp [hm]
    -- Step 5: Assemble a countable open cover of `X` using the isolating neighbourhoods
    --         and the open complement of the closed set `B`.
    let cover : ℕ → Set X
      | 0 => Bᶜ
      | Nat.succ n => V n
    -- Step 5.1: Every member of the cover is open.
    have hCover_open : ∀ n, IsOpen (cover n) := by
      intro n
      cases n with
      | zero =>
          -- `Bᶜ` is open because `B` is closed.
          simpa [cover] using hB_closed.isOpen_compl
      | succ n =>
          simpa [cover] using hV_open n
    -- Step 5.2: The cover actually covers the whole space.
    have hCover_all : (Set.univ : Set X) ⊆ ⋃ n, cover n := by
      intro x _
      -- Step 5.2.1: Either `x` comes from the sampled set `B` or it does not.
      by_cases hxB : x ∈ B
      · rcases hxB with ⟨n, rfl⟩
        have : b n ∈ cover (Nat.succ n) := by simpa [cover] using hb_in_V n
        exact Set.mem_iUnion.2 ⟨Nat.succ n, this⟩
      · have : x ∈ cover 0 := by simp [cover, hxB]
        exact Set.mem_iUnion.2 ⟨0, this⟩
    -- Step 6: Countable compactness provides a finite subcover of our explicit cover.
    obtain ⟨t, ht⟩ := hcc cover ⟨hCover_open, hCover_all⟩
    -- Step 6.1: Extract a finite list of indices that could possibly cover points of `B`.
    let pre : Finset ℕ := (t.filter fun n => n ≠ 0).image Nat.pred
    -- Step 6.2: If `m ∉ pre`, then `Nat.succ m ∉ t` (otherwise `m` would be captured by `pre`).
    have hSucc_not_in : ∀ m, m ∉ pre → Nat.succ m ∉ t := by
      intro m hmNot
      by_contra hSucc
      have hSucc_ne : Nat.succ m ≠ 0 := Nat.succ_ne_zero _
      have hSucc_filter : Nat.succ m ∈ t.filter (fun n => n ≠ 0) :=
        Finset.mem_filter.mpr ⟨hSucc, by simp⟩
      have hPred_in : m ∈ pre := by
        refine Finset.mem_image.mpr ?_
        refine ⟨Nat.succ m, hSucc_filter, ?_⟩
        simp
      exact hmNot hPred_in
    -- Step 6.3: Choose an index `m` whose successor is missing from the finite subcover.
    obtain ⟨m, _, hmNotPre⟩ :=
      (Set.infinite_univ : (Set.univ : Set ℕ).Infinite).exists_notMem_finset pre
    have hSucc_m_not : Nat.succ m ∉ t := hSucc_not_in m hmNotPre
    -- Step 7: Show that `b m` is not covered by the finite subcover, contradicting `ht`.
    have hb_not_covered : b m ∉ ⋃ i ∈ t, cover i := by
      intro hIn
      rcases Set.mem_iUnion.1 hIn with ⟨i, hi⟩
      rcases Set.mem_iUnion.1 hi with ⟨hi_t, hmem_cover⟩
      cases i with
      | zero =>
          -- Step 7.1: `cover 0 = Bᶜ`, but `b m` lies in `B`.
          have hBmem : b m ∈ B := ⟨m, rfl⟩
          have hBnot : b m ∉ B := by simpa [cover] using hmem_cover
          exact hBnot hBmem
      | succ k =>
          -- Step 7.2: Membership in `cover (succ k)` forces `k = m`,
          --           hence `succ m ∈ t`, contradiction.
          have hkEq : k = m := hV_hits_only (by simpa [cover] using hmem_cover)
          have : Nat.succ m ∈ t := by simpa [hkEq] using hi_t
          exact hSucc_m_not this
    -- Step 7.3: Apply the supposed finite cover to `b m` to obtain the contradiction.
    have hb_in_union : b m ∈ ⋃ i ∈ t, cover i := ht (by simp)
    exact hb_not_covered hb_in_union
  · -- Reverse direction: limit point compact (strong) → countably compact.
    -- Step 8: Assume limit point compactness (strong) holds; we must show
    --         countable compactness.
    intro hLPC U ⟨hOpen, hCover⟩
    -- Step 8.2: Argue by contradiction: assume no finite subcover exists.
    by_contra hNoFin
    push_neg at hNoFin
    -- Step 9: For each n, pick x_n ∉ U_0 ∪ ... ∪ U_n (possible since no finite subcover).
    have hNotCovered : ∀ n, ∃ x : X, x ∉ ⋃ i ∈ Finset.range (n + 1), U i := by
      intro n
      by_contra hall
      push_neg at hall
      exact hNoFin (Finset.range (n + 1)) (fun x _ => hall x)
    classical
    choose x hx using hNotCovered
    -- Step 10: The set A = range x is infinite.
    have hA_inf : (Set.range x).Infinite := by
      -- Step 10.1: Suppose A = range x is finite.
      intro hFin
      -- Step 10.2: Since A is finite and each point is in the full cover,
      --   there exists a finite index set covering all of A.
      have hA_sub : Set.range x ⊆ ⋃ i, U i := fun z _ => hCover (Set.mem_univ z)
      -- Step 10.3: Since range x is finite, it's covered by finitely many U i.
      obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, Set.range x ⊆ ⋃ i ∈ S, U i := by
        have := hFin.isCompact.elim_finite_subcover U hOpen (fun z hz =>
          Set.mem_iUnion.mpr (Set.mem_iUnion.mp (hA_sub hz)))
        obtain ⟨t, ht⟩ := this
        exact ⟨t, ht⟩
      -- Step 10.4: Let M = max element of S (or 0).
      let M := S.sup id
      -- Step 10.5: x M ∈ range x ⊆ ⋃ i ∈ S, U i ⊆ ⋃ i ∈ range(M+1), U i.
      have hxM_in_A : x M ∈ Set.range x := ⟨M, rfl⟩
      have hxM_in_S_union : x M ∈ ⋃ i ∈ S, U i := hS hxM_in_A
      have hS_sub_range : S ⊆ Finset.range (M + 1) := by
        intro i hi
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
      have hxM_in_range_union : x M ∈ ⋃ i ∈ Finset.range (M + 1), U i :=
        Set.biUnion_subset_biUnion_left (Finset.coe_subset.mpr hS_sub_range) hxM_in_S_union
      -- Step 10.6: But hx M says x M ∉ ⋃ i ∈ range(M+1), U i. Contradiction.
      exact hx M hxM_in_range_union
    -- Step 11: By limit point compactness (strong), A has an accumulation point y.
    obtain ⟨y, hy_cluster⟩ := hLPC (Set.range x) hA_inf.to_subtype
    -- Step 12: y is in the full cover, so y ∈ U N for some N.
    obtain ⟨N, hyN⟩ := Set.mem_iUnion.mp (hCover (Set.mem_univ y))
    -- Step 12.1: Build W = (⋃ i ∈ range(N+1), U i) \ ({x 0,...,x N} \ {y}), a nbhd of y.
    --   Key: W is open because it's an open set minus a finite closed set (T1).
    --   W avoids all x_i: for i ≤ N, x_i ∈ {x 0,...,x N}\{y} (if x_i ≠ y) so x_i ∉ W.
    --   For i > N: x_i ∉ U_0∪...∪U_N (since N < i means N ∈ range(i+1), so hx i applies).
    --   So W ∩ (range x \ {y}) = ∅, contradicting clustering.
    let bigU := ⋃ i ∈ Finset.range (N + 1), U i
    let pts := ((Finset.range (N + 1)).image x : Finset X)
    have hbigU_open : IsOpen bigU := isOpen_biUnion (fun i _ => hOpen i)
    have hbigU_nhds : bigU ∈ 𝓝 y := hbigU_open.mem_nhds
      (Set.mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_refl N))) hyN)
    -- Step 12.2: The set pts \ {y} is finite and closed (T1).
    have hpts_minus_y_closed : IsClosed ((pts : Set X) \ {y}) :=
      (pts.finite_toSet.subset Set.diff_subset).isClosed
    -- Step 12.3: W = bigU \ (pts \ {y}) is open and contains y.
    let W := bigU \ ((pts : Set X) \ {y})
    have hW_open : IsOpen W := hbigU_open.sdiff hpts_minus_y_closed
    have hy_in_W : y ∈ W := by
      refine ⟨Set.mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_refl N))) hyN, ?_⟩
      simp [Set.mem_diff, Set.mem_singleton_iff]
    have hW_nhds : W ∈ 𝓝 y := hW_open.mem_nhds hy_in_W
    -- Step 12.4: W ∩ (range x \ {y}) = ∅.
    have hW_disjoint : W ∩ (Set.range x \ {y}) = ∅ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro ⟨hzU, hzNotPts⟩ ⟨⟨m, hm⟩, hzNe⟩
      subst hm
      -- Case split: m ≤ N or m > N.
      by_cases hmN : m < N + 1
      · -- Case m ≤ N: x m ∈ pts, and x m ≠ y (since z ≠ y), so x m ∈ pts \ {y}.
        have hxm_pts : x m ∈ (pts : Set X) :=
          Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hmN, rfl⟩)
        exact hzNotPts ⟨hxm_pts, hzNe⟩
      · -- Case m > N: x m ∉ bigU because x m ∉ ⋃ i ∈ range(m+1), U i and range(N+1) ⊆ range(m+1).
        push_neg at hmN
        have hrange_sub : Finset.range (N + 1) ⊆ Finset.range (m + 1) :=
          Finset.range_mono (by omega)
        have hxm_not : x m ∉ ⋃ i ∈ Finset.range (m + 1), U i := hx m
        have hxm_not_bigU : x m ∉ bigU := fun h =>
          hxm_not (Set.biUnion_subset_biUnion_left (Finset.coe_subset.mpr hrange_sub) h)
        exact hxm_not_bigU hzU
    -- Step 12.5: Clustering says W ∩ (range x \ {y}) is nonempty. Contradiction.
    have hMeet := (clusterPt_principal_iff.mp hy_cluster) W hW_nhds
    rw [Set.nonempty_iff_ne_empty] at hMeet
    exact hMeet hW_disjoint
