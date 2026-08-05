import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset Set
open scoped BigOperators



/-Informal Statement

Prove that every open set in $\mathbb{R}$ is the union of an at most countable collection of disjoint segments.
-/

/-Informal Proof

Let $O$ be open. For each pair of points $x \in O, y \in O$, we define an equivalence relation $x \sim y$ by saying $x \sim y$ if and only if $[\min (x, y), \max (x, y)] \subset$ 0 . This is an equivalence relation, since $x \sim x([x, x] \subset O$ if $x \in O)$; if $x \sim y$, then $y \sim x$ (since $\min (x, y)=\min (y, x)$ and $\max (x, y)=\max (y, x))$; and if $x \sim y$ and $y \sim z$, then $x \sim z([\min (x, z), \max (x, z)] \subseteq[\min (x, y), \max (x, y)] \cup$ $[\min (y, z), \max (y, z)] \subseteq O)$. In fact it is easy to prove that
$$
\min (x, z) \geq \min (\min (x, y), \min (y, z))
$$
and
$$
\max (x, z) \leq \max (\max (x, y), \max (y, z))
$$
It follows that $O$ can be written as a disjoint union of pairwise disjoint equivalence classes. We claim that each equivalence class is an open interval.

To show this, for each $x \in O$; let $A=\{z:[z, x] \subseteq O\}$ and $B=\{z:[x, z] \subseteq$ $O\}$, and let $a=\inf A, b=\sup B$. We claim that $(a, b) \subset O$. Indeed if $a<z<b$, there exists $c \in A$ with $c<z$ and $d \in B$ with $d>z$. Then $z \in[c, x] \cup[x, d] \subseteq O$. We now claim that $(a, b)$ is the equivalence class containing $x$. It is clear that each element of $(a, b)$ is equivalent to $x$ by the way in which $a$ and $b$ were chosen. We need to show that if $z \notin(a, b)$, then $z$ is not equivalent to $x$. Suppose that $z<a$. If $z$ were equivalent to $x$, then $[z, x]$ would be contained in $O$, and so we would have $z \in A$. Hence $a$ would not be a lower bound for $A$. Similarly if $z>b$ and $z \sim x$, then $b$ could not be an upper bound for $B$.

We have now established that $O$ is a union of pairwise disjoint open intervals. Such a union must be at most countable, since each open interval contains a rational number not in any other interval.
-/

theorem Rudin_exercise_2_29 (U : Set ℝ) (hU : IsOpen U) :
  ∃ (f : ℕ → Set ℝ), (∀ n, ∃ a b : ℝ, f n = {x | a < x ∧ x < b}) ∧ (∀ n, f n ⊆ U) ∧
  (∀ n m, n ≠ m → f n ∩ f m = ∅) ∧
  U = ⋃ n, f n := by
  sorry

/-
Step 0.1: The statement above is false because the set `U = {x : ℝ | 0 < x}` is open and connected,
but it cannot be partitioned into pairwise disjoint bounded open segments (each of the form
`{x | a < x ∧ x < b}` with finite endpoints).
Step 0.2: If `U` were such a disjoint union, the connectedness of `U` would force the union to
consist of a single segment, yet `(0, ∞)` is not of the prescribed form since it has no finite
upper endpoint.  Hence the original claim misses the possibility of unbounded components.
-/

noncomputable section

open Classical
open scoped Topology

private lemma ioi_ne_ioo (a b : ℝ) : Set.Ioi (0 : ℝ) ≠ Set.Ioo a b := by
  -- Step 1: Assume equality and aim for contradiction via a point dominating any upper bound.
  intro h
  -- Step 2: Use the point `y = max b 1`, which certainly lies in `(0, ∞)`.
  set y : ℝ := max b 1 with hy
  have hy_pos : 0 < y := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hy_mem_Ioi : y ∈ Set.Ioi (0 : ℝ) := hy_pos
  -- Step 3: Transport membership through the assumed equality.
  have hy_mem_Ioo : y ∈ Set.Ioo a b := by simpa [h] using hy_mem_Ioi
  -- Step 4: But `y` cannot lie in the bounded interval because it dominates `b`.
  have hy_not : y ∉ Set.Ioo a b := by
    intro hy'
    exact (not_lt_of_ge (le_max_left _ _)) hy'.2
  exact hy_not hy_mem_Ioo

theorem Rudin_exercise_2_29_neg : ¬ (∀ (U : Set ℝ), IsOpen U →
    ∃ (f : ℕ → Set ℝ),
      (∀ n, ∃ a b : ℝ, f n = {x | a < x ∧ x < b}) ∧
      (∀ n, f n ⊆ U) ∧
      (∀ n m, n ≠ m → f n ∩ f m = ∅) ∧
      U = ⋃ n, f n) := by
  classical
  -- Step 1: Suppose the original claim holds and derive data for the open ray `(0, ∞)`.
  intro hStatement
  obtain ⟨f, hfInterval, hfSubset, hfDisjoint, hUnion⟩ :=
    hStatement (Set.Ioi (0 : ℝ)) isOpen_Ioi
  -- Step 2: Each set `f n` is open because it is an open segment.
  have hfOpen : ∀ n, IsOpen (f n) := by
    intro n
    obtain ⟨a, b, hfn⟩ := hfInterval n
    simpa [hfn, Set.Ioo] using (isOpen_Ioo : IsOpen (Set.Ioo a b))
  -- Step 3: Pick an index containing the point `1`.
  have hone : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have hone_union : (1 : ℝ) ∈ ⋃ n, f n := by simpa [hUnion] using hone
  obtain ⟨n₀, hn₀⟩ := Set.mem_iUnion.mp hone_union
  -- Step 4: Split the cover into the chosen component and all other components.
  let V : Set ℝ := ⋃ (p : {m // m ≠ n₀}), f p
  have hVOpen : IsOpen V := by
    refine isOpen_iUnion fun p => ?_
    simpa using hfOpen p
  -- Step 5: Use pairwise disjointness to show `f n₀` is disjoint from `V`.
  have hDisj : Disjoint (f n₀) V := by
    refine Set.disjoint_iUnion_right.2 ?_
    intro p
    have hpair : f n₀ ∩ f (p : ℕ) = ∅ := hfDisjoint _ _ p.property.symm
    exact Set.disjoint_iff_inter_eq_empty.2 (by simpa using hpair)
  -- Step 6: Show that `(0, ∞)` is covered by `f n₀` together with `V`.
  have hCoverSplit : Set.Ioi (0 : ℝ) ⊆ f n₀ ∪ V := by
    intro x hx
    have hx_union : x ∈ ⋃ n, f n := by simpa [hUnion] using hx
    rcases Set.mem_iUnion.1 hx_union with ⟨n, hxn⟩
    by_cases hn : n = n₀
    · subst hn; exact Or.inl hxn
    · refine Or.inr ?_
      refine Set.mem_iUnion.2 ⟨⟨n, hn⟩, ?_⟩
      simpa using hxn
  -- Step 7: The intersection of `(0, ∞)` with `f n₀` is nonempty (contains `1`).
  have hIntersect :
      (Set.Ioi (0 : ℝ) ∩ f n₀).Nonempty := ⟨1, hone, hn₀⟩
  -- Step 8: Connectedness of `(0, ∞)` forces it to lie entirely inside `f n₀`.
  have hSubset :
      Set.Ioi (0 : ℝ) ⊆ f n₀ :=
    isPreconnected_Ioi.subset_left_of_subset_union
      (hu := hfOpen n₀) (hv := hVOpen) (huv := hDisj)
      (hsuv := hCoverSplit) (hsu := hIntersect)
  -- Step 9: Combine with the cover inclusion to get equality of sets.
  have hSubset' : f n₀ ⊆ Set.Ioi (0 : ℝ) := hfSubset n₀
  have hEq : Set.Ioi (0 : ℝ) = f n₀ := by
    exact Set.Subset.antisymm hSubset hSubset'
  -- Step 10: Substitute the explicit description of `f n₀` and obtain a contradiction.
  obtain ⟨a, b, hfn⟩ := hfInterval n₀
  have hImpossible : Set.Ioi (0 : ℝ) = Set.Ioo a b := by
    simpa [hfn, Set.Ioo] using hEq
  exact (ioi_ne_ioo a b) hImpossible

/-
## Why the Original Formalization is Not Faithful

The original formalization `Rudin_exercise_2_29` has two issues:

1. The segments use real endpoints `a b : ℝ`, so each segment is a *bounded* open interval
   `{x | a < x ∧ x < b}`. This cannot express unbounded intervals like `(0, ∞)` or `(-∞, 0)`
   that appear as connected components of open sets in ℝ. The counterexample above shows
   this makes the original statement false.

2. The "corrected" version `Rudin_exercise_2_29_corrected` (with `IsConnected U` added) fixes
   the endpoint issue by using `EReal`, but adds a **spurious hypothesis** `IsConnected U`.
   The informal statement says "every open set in ℝ", not just connected ones. Adding
   connectedness makes the theorem a strict special case (logically weaker) of the informal
   claim — a connected open subset of ℝ is just a single interval, making the decomposition
   trivial.

## Correction

- Remove the `IsConnected U` hypothesis to match the informal "every open set".
- Use `EReal` endpoints to accommodate unbounded segments.
- The proof is left as sorry since it requires constructing the countable decomposition into
  connected components (a nontrivial argument involving the equivalence relation from Rudin's
  proof and the density of ℚ).
-/

theorem Rudin_exercise_2_29_corrected (U : Set ℝ) (hU : IsOpen U) :
  ∃ (f : ℕ → Set ℝ),
    (∀ n, ∃ a b : EReal, f n = {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}) ∧
    (∀ n, f n ⊆ U) ∧
    (∀ n m, n ≠ m → f n ∩ f m = ∅) ∧
    U = ⋃ n, f n := by
  classical
  -- Step 1: Prove the interval-shape lemma needed for the components.
  -- Step 1.1: The lemma says that every open preconnected subset of `ℝ` is an open interval
  -- with endpoints allowed in `EReal`, so it may be bounded, left-unbounded, right-unbounded,
  -- all of `ℝ`, or empty.
  have h_open_preconnected_eq_EReal_Ioo :
      ∀ {s : Set ℝ}, IsOpen s → IsPreconnected s →
        ∃ a b : EReal, s = {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b} := by
    intro s hs_open hs_pre
    -- Step 1.2: First dispose of the empty-set case; it is the interval `(0, 0)`.
    by_cases hs_empty : s = ∅
    · refine ⟨0, 0, ?_⟩
      ext x
      constructor
      · intro hx
        rw [hs_empty] at hx
        exact hx.elim
      · rintro ⟨h0x, hx0⟩
        exact False.elim ((not_lt_of_ge (le_of_lt h0x)) hx0)
    · -- Step 1.3: In the nonempty case, define the lower and upper endpoints in `EReal`.
      let S : Set EReal := (fun x : ℝ => (x : EReal)) '' s
      let a : EReal := sInf S
      let b : EReal := sSup S
      refine ⟨a, b, ?_⟩
      -- Step 1.4: Prove equality by pointwise extensionality.
      ext x
      constructor
      · intro hx
        -- Step 1.5: If `x ∈ s`, openness gives a small ball around `x` contained in `s`.
        obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.isOpen_iff.mp hs_open x hx
        -- Step 1.6: Move a little to the left while staying in `s`.
        let y : ℝ := x - ε / 2
        have hy_lt_x : y < x := by
          dsimp [y]
          linarith
        have hy_mem_ball : y ∈ Metric.ball x ε := by
          rw [Metric.mem_ball, Real.dist_eq]
          have hyx : y - x = -ε / 2 := by
            dsimp [y]
            ring
          rw [hyx, abs_of_neg]
          · linarith
          · linarith
        have hy_mem : y ∈ s := hε_sub hy_mem_ball
        have hy_mem_S : (y : EReal) ∈ S := ⟨y, hy_mem, rfl⟩
        -- Step 1.7: Since `a` is the infimum of all points of `s`, `a ≤ y < x`.
        have ha_le_y : a ≤ (y : EReal) := sInf_le hy_mem_S
        have hy_lt_x_E : (y : EReal) < (x : EReal) := by
          exact EReal.coe_lt_coe_iff.mpr hy_lt_x
        have ha_lt_x : a < (x : EReal) := lt_of_le_of_lt ha_le_y hy_lt_x_E
        -- Step 1.8: Move a little to the right while staying in `s`.
        let z : ℝ := x + ε / 2
        have x_lt_z : x < z := by
          dsimp [z]
          linarith
        have hz_mem_ball : z ∈ Metric.ball x ε := by
          rw [Metric.mem_ball, Real.dist_eq]
          have hzx : z - x = ε / 2 := by
            dsimp [z]
            ring
          rw [hzx, abs_of_pos]
          · linarith
          · linarith
        have hz_mem : z ∈ s := hε_sub hz_mem_ball
        have hz_mem_S : (z : EReal) ∈ S := ⟨z, hz_mem, rfl⟩
        -- Step 1.9: Since `b` is the supremum of all points of `s`, `x < z ≤ b`.
        have hz_le_b : (z : EReal) ≤ b := le_sSup hz_mem_S
        have hx_lt_z_E : (x : EReal) < (z : EReal) := by
          exact EReal.coe_lt_coe_iff.mpr x_lt_z
        have hx_lt_b : (x : EReal) < b := lt_of_lt_of_le hx_lt_z_E hz_le_b
        exact ⟨ha_lt_x, hx_lt_b⟩
      · -- Step 1.10: Conversely, suppose `x` lies strictly between the EReal endpoints.
        rintro ⟨ha_lt_x, hx_lt_b⟩
        -- Step 1.11: The inequality `a < x` produces a point `y ∈ s` with `y < x`.
        obtain ⟨ey, hey_mem, hey_lt_x⟩ := sInf_lt_iff.mp ha_lt_x
        rcases hey_mem with ⟨y, hy_mem, rfl⟩
        have hy_lt_x : y < x := EReal.coe_lt_coe_iff.mp hey_lt_x
        -- Step 1.12: The inequality `x < b` produces a point `z ∈ s` with `x < z`.
        obtain ⟨ez, hez_mem, hx_lt_ez⟩ := lt_sSup_iff.mp hx_lt_b
        rcases hez_mem with ⟨z, hz_mem, rfl⟩
        have hx_lt_z : x < z := EReal.coe_lt_coe_iff.mp hx_lt_ez
        -- Step 1.13: Preconnected subsets of a linear order are order-connected, so the whole
        -- closed interval from `y` to `z` lies in `s`; in particular, `x ∈ s`.
        exact hs_pre.Icc_subset hy_mem hz_mem ⟨le_of_lt hy_lt_x, le_of_lt hx_lt_z⟩
  -- Step 2: Define the collection of all connected components of `U` which actually meet `U`.
  let C : Set (Set ℝ) := {V : Set ℝ | ∃ x ∈ U, V = connectedComponentIn U x}
  -- Step 2.1: Every component in `C` is open.
  have hC_open : ∀ V ∈ C, IsOpen V := by
    intro V hV
    rcases hV with ⟨x, hxU, rfl⟩
    exact hU.connectedComponentIn
  -- Step 2.2: Every component in `C` is nonempty, since it contains its base point.
  have hC_nonempty : ∀ V ∈ C, V.Nonempty := by
    intro V hV
    rcases hV with ⟨x, hxU, rfl⟩
    exact ⟨x, mem_connectedComponentIn hxU⟩
  -- Step 2.3: Every component in `C` is contained in `U`.
  have hC_subset : ∀ V ∈ C, V ⊆ U := by
    intro V hV
    rcases hV with ⟨x, hxU, rfl⟩
    exact connectedComponentIn_subset U x
  -- Step 2.4: Distinct components in `C` are disjoint.
  have hC_pairwise : C.PairwiseDisjoint id := by
    intro V hV W hW hVW
    rw [Function.onFun]
    -- Step 2.4.1: Unpack the two components.
    rcases hV with ⟨x, hxU, rfl⟩
    rcases hW with ⟨y, hyU, rfl⟩
    -- Step 2.4.2: It is enough to prove that no point lies in both components.
    rw [Set.disjoint_iff_inter_eq_empty]
    by_contra hne
    -- Step 2.4.3: If the intersection is nonempty, choose a common point `z`.
    obtain ⟨z, hz_mem⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hz_x : z ∈ connectedComponentIn U x := hz_mem.1
    have hz_y : z ∈ connectedComponentIn U y := hz_mem.2
    -- Step 2.4.4: A common point forces the two connected components to be equal.
    have hxz : connectedComponentIn U x = connectedComponentIn U z :=
      connectedComponentIn_eq hz_x
    have hyz : connectedComponentIn U y = connectedComponentIn U z :=
      connectedComponentIn_eq hz_y
    exact hVW (hxz.trans hyz.symm)
  -- Step 2.5: Therefore the component family is countable, because `ℝ` is separable and a
  -- disjoint family of nonempty open sets in a separable space is countable.
  have hC_countable : C.Countable :=
    hC_pairwise.countable_of_isOpen hC_open hC_nonempty
  -- Step 3: Put an encodable structure on the countable component set.
  letI : Encodable C := hC_countable.toEncodable
  -- Step 3.1: Enumerate components injectively by their `Encodable.encode` values.  If an index
  -- does not encode any component, we place the empty set there.
  let f : ℕ → Set ℝ := fun n =>
    if h : ∃ V : C, Encodable.encode V = n then ((Classical.choose h : C) : Set ℝ) else ∅
  -- Step 3.2: Record the defining equation at an index that encodes a component.
  have hf_of_exists : ∀ {n : ℕ} (h : ∃ V : C, Encodable.encode V = n),
      f n = ((Classical.choose h : C) : Set ℝ) := by
    intro n h
    dsimp [f]
    rw [dif_pos h]
  -- Step 3.3: Record the defining equation at an unused index.
  have hf_of_not_exists : ∀ {n : ℕ} (h : ¬ ∃ V : C, Encodable.encode V = n),
      f n = ∅ := by
    intro n h
    dsimp [f]
    rw [dif_neg h]
  -- Step 3.4: At a component's own encoded index, the enumeration returns exactly that component.
  have hf_encode : ∀ V : C, f (Encodable.encode V) = (V : Set ℝ) := by
    intro V
    have h_exists : ∃ W : C, Encodable.encode W = Encodable.encode V := ⟨V, rfl⟩
    rw [hf_of_exists h_exists]
    have h_choose_encode : Encodable.encode (Classical.choose h_exists : C) = Encodable.encode V :=
      Classical.choose_spec h_exists
    have h_choose_eq : (Classical.choose h_exists : C) = V :=
      Encodable.encode_injective h_choose_encode
    exact congrArg Subtype.val h_choose_eq
  -- Step 3.5: Every enumerated nonempty entry is a genuine component in `C`.
  have hf_mem_C_or_empty : ∀ n, f n ∈ C ∨ f n = ∅ := by
    intro n
    by_cases h : ∃ V : C, Encodable.encode V = n
    · left
      rw [hf_of_exists h]
      exact (Classical.choose h).property
    · right
      exact hf_of_not_exists h
  -- Step 4: Prove that every `f n` has the required EReal interval form.
  have hf_interval :
      ∀ n, ∃ a b : EReal, f n = {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b} := by
    intro n
    rcases hf_mem_C_or_empty n with hmem | hempty
    · -- Step 4.1: A genuine component is open and preconnected, hence has the interval form.
      have hopen : IsOpen (f n) := hC_open (f n) hmem
      have hpre : IsPreconnected (f n) := by
        rcases hmem with ⟨x, hxU, hfx⟩
        rw [hfx]
        exact isPreconnected_connectedComponentIn
      exact h_open_preconnected_eq_EReal_Ioo hopen hpre
    · -- Step 4.2: An unused index is empty, represented as `(0, 0)`.
      refine ⟨0, 0, ?_⟩
      ext x
      constructor
      · intro hx
        rw [hempty] at hx
        exact hx.elim
      · rintro ⟨h0x, hx0⟩
        exact False.elim ((not_lt_of_ge (le_of_lt h0x)) hx0)
  -- Step 5: Prove that every enumerated set is contained in `U`.
  have hf_subset : ∀ n, f n ⊆ U := by
    intro n
    rcases hf_mem_C_or_empty n with hmem | hempty
    · exact hC_subset (f n) hmem
    · rw [hempty]
      exact empty_subset U
  -- Step 6: Prove pairwise disjointness of the sequence.
  have hf_pairwise : ∀ n m, n ≠ m → f n ∩ f m = ∅ := by
    intro n m hnm
    rcases hf_mem_C_or_empty n with hnC | hn_empty
    · rcases hf_mem_C_or_empty m with hmC | hm_empty
      · -- Step 6.1: If both entries are components, prove they cannot be the same component.
        have hneq_sets : f n ≠ f m := by
          intro hsets
          -- Step 6.1.1: Recover encoded representatives for both nonempty component entries.
          by_cases hn_exists : ∃ V : C, Encodable.encode V = n
          · by_cases hm_exists : ∃ W : C, Encodable.encode W = m
            · have hn_eq :
                  f n = ((Classical.choose hn_exists : C) : Set ℝ) :=
                hf_of_exists hn_exists
              have hm_eq :
                  f m = ((Classical.choose hm_exists : C) : Set ℝ) :=
                hf_of_exists hm_exists
              have hsub_eq :
                  (Classical.choose hn_exists : C) = Classical.choose hm_exists := by
                apply Subtype.ext
                simpa [hn_eq, hm_eq] using hsets
              have hn_code : Encodable.encode (Classical.choose hn_exists : C) = n :=
                Classical.choose_spec hn_exists
              have hm_code : Encodable.encode (Classical.choose hm_exists : C) = m :=
                Classical.choose_spec hm_exists
              exact hnm (by
                rw [← hn_code, ← hm_code, hsub_eq])
            · have : f m = ∅ := hf_of_not_exists hm_exists
              exact (hC_nonempty (f n) hnC).ne_empty (by simpa [this] using hsets)
          · have : f n = ∅ := hf_of_not_exists hn_exists
            exact (hC_nonempty (f m) hmC).ne_empty (by simpa [this] using hsets.symm)
        -- Step 6.2: Distinct components are disjoint.
        exact Set.disjoint_iff_inter_eq_empty.mp (hC_pairwise hnC hmC hneq_sets)
      · -- Step 6.3: If the right entry is empty, the intersection is empty.
        simp [hm_empty]
    · -- Step 6.4: If the left entry is empty, the intersection is empty.
      simp [hn_empty]
  -- Step 7: Prove that the union of the enumerated components is exactly `U`.
  have hf_union : U = ⋃ n, f n := by
    ext x
    constructor
    · intro hxU
      -- Step 7.1: A point of `U` lies in its own connected component.
      let V : C := ⟨connectedComponentIn U x, ⟨x, hxU, rfl⟩⟩
      have hxV : x ∈ (V : Set ℝ) := mem_connectedComponentIn hxU
      -- Step 7.2: The component appears at its encoded index.
      refine Set.mem_iUnion.2 ⟨Encodable.encode V, ?_⟩
      simpa [hf_encode V] using hxV
    · intro hxUnion
      -- Step 7.3: Conversely, every enumerated component is contained in `U`, and empty entries
      -- contribute no points.
      rcases Set.mem_iUnion.1 hxUnion with ⟨n, hxn⟩
      exact hf_subset n hxn
  -- Step 8: Assemble the sequence and all required properties.
  exact ⟨f, hf_interval, hf_subset, hf_pairwise, hf_union⟩
