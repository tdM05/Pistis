import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Show that if $X$ is regular, every pair of points of $X$ have neighborhoods whose closures are disjoint.
-/

/-Informal Proof

Let $x, y \in X$ be two points such that $x \neq y$. Since $X$ is regular (and thus Hausdorff), there exist disjoint open sets $U, V \subseteq X$ such that $x \in U$ and $y \in V$.
Note that $y \notin \bar{U}$. Otherwise $V$ must intersect $U$ in a point different from $y$ since $V$ is an open neighborhood of $y$, which is a contradiction since $U$ and $V$ are disjoint.
Since $X$ is regular and $\bar{U}$ is closed, there exist disjoint open sets $U^{\prime}, V^{\prime} \subseteq X$ such that $\bar{U} \subseteq U^{\prime}$ and $y \in V^{\prime}$.

And now $U$ and $V^{\prime}$ are neighborhoods of $x$ and $y$ whose closures are disjoint. If $\bar{U} \cap \overline{V^{\prime}} \neq \emptyset$, then it follows that $U^{\prime} \supseteq U$ intersects $\overline{V^{\prime}}$. Since $U^{\prime}$ is open, it follows that $U^{\prime}$ intersects $V^{\prime}$, which is a contradiction.
-/

theorem Munkres_exercise_31_1 {X : Type*} [TopologicalSpace X]
  (hX : RegularSpace X) (x y : X) (hxy : x ≠ y) :
  ∃ (U V : Set X), IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ closure U ∩ closure V = ∅ := by
  sorry

/-
The statement above is false: consider `Y = ℝ × Bool` endowed with the topology induced by the
projection onto the first coordinate. This topology makes `Y` a regular space (because it is
induced from the regular space `ℝ`), but the two distinct points `(r, true)` and `(r, false)` have
exactly the same open neighbourhoods, so no pair of open sets can separate them, and a fortiori
their closures can never be disjoint.
-/

theorem Munkres_exercise_31_1_neg :
    ¬ (∀ (X : Type*) [TopologicalSpace X], RegularSpace X →
        ∀ x y : X, x ≠ y →
          ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧
            closure U ∩ closure V = (∅ : Set X)) := by
  classical
  -- Step 1: Build the counterexample space consisting of two indistinguishable copies of ℝ.
  let B := ℝ × Bool
  -- Step 1.1: Equip `B` with the topology induced by the projection to ℝ.
  letI : TopologicalSpace B := induced Prod.fst inferInstance
  -- Step 1.2: Because induced topologies preserve regularity, `B` is regular.
  haveI : RegularSpace B := regularSpace_induced Prod.fst
  -- Step 1.3: Lift `B` to an arbitrary universe so it can instantiate the quantified variable.
  let X := ULift B
  letI : TopologicalSpace X := induced ULift.down inferInstance
  haveI : RegularSpace X := regularSpace_induced ULift.down
  -- Step 2: Choose the two distinct points occupying the same real coordinate.
  let x : X := ⟨(0, true)⟩
  let y : X := ⟨(0, false)⟩
  have hxy : x ≠ y := by
    -- Step 2.1: Distinguish the second coordinates to prove the inequality.
    intro h
    have := congrArg (fun z : X => (ULift.down z).2) h
    simp [x, y] at this
  -- Step 3: Assume the false universal statement and derive the contradictory separating opens.
  intro h
  -- Step 3.1: Specialize the universal statement to the lifted counterexample space.
  have hX := h (X := X)
  have hXreg := hX (inferInstance : RegularSpace X)
  obtain ⟨U, V, hUopen, hVopen, hxU, hyV, hcl⟩ := hXreg x y hxy
  -- Step 4: Unpack that opens in the induced topology are nested preimages of opens in ℝ.
  rcases (isOpen_induced_iff.mp hUopen) with ⟨W, hWopen, hUeq⟩
  rcases (isOpen_induced_iff.mp hWopen) with ⟨U₀, hU₀open, hWeq⟩
  -- Step 5: Any open containing the lift of `(0, true)` also contains the lift of `(0, false)`.
  have hxU_pre : x ∈ ULift.down ⁻¹' W := by simpa [hUeq] using hxU
  have hxW_mem : ULift.down x ∈ W := by simpa [Set.preimage] using hxU_pre
  have hxCoord : (0 : ℝ) ∈ U₀ := by
    have : ULift.down x ∈ Prod.fst ⁻¹' U₀ := by simpa [hWeq] using hxW_mem
    simpa [Set.preimage, x] using this
  have hyCoord : (0 : ℝ) ∈ U₀ := hxCoord
  have hyW_mem : ULift.down y ∈ W := by
    have : ULift.down y ∈ Prod.fst ⁻¹' U₀ := by simpa [Set.preimage, y] using hyCoord
    simpa [hWeq] using this
  have hyU_pre : y ∈ ULift.down ⁻¹' W := by simpa [Set.preimage] using hyW_mem
  have hyU : y ∈ U := by simpa [hUeq] using hyU_pre
  -- The original hypothesis already provides `y ∈ V`.
  -- Step 6: The point `x` lies in both closures, contradicting the claimed empty intersection.
  have hy_inter : y ∈ closure U ∩ closure V := ⟨subset_closure hyU, subset_closure hyV⟩
  have hy_inter_nonempty : (closure U ∩ closure V).Nonempty := ⟨y, hy_inter⟩
  have : False := by simp [hcl] at hy_inter_nonempty
  exact this.elim

/-
The original formalization is not faithful to the informal statement.

The informal statement's hypothesis is that X is "regular" in Munkres' sense (T1 + regular,
i.e., T3), and the conclusion is that any two distinct points have neighborhoods with disjoint
closures (the T2.5 property). The Lean formalization replaces the hypothesis "regular" with
`[T25Space X]`, which already asserts exactly the conclusion — making the theorem a tautology
("T2.5 implies T2.5") rather than the substantive "T3 implies T2.5".

The correction uses `[RegularSpace X]` and `[T1Space X]` separately (which together give
Munkres' "regular" = T3). In Mathlib, `RegularSpace + T1Space` implies `T3Space`, which in
turn implies `T25Space` (via `T3Space.t25Space`), so the conclusion follows.
-/

theorem Munkres_exercise_31_1_corrected {X : Type*} [TopologicalSpace X]
    [RegularSpace X] [T1Space X]
    (x y : X) (hxy : x ≠ y) :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧
      closure U ∩ closure V = (∅ : Set X) := by
  classical
  -- Step 1: RegularSpace + T1Space gives T3Space, which implies T2.5 in Mathlib.
  haveI : T25Space X := T3Space.t25Space
  -- Step 2: Use the T2.5 separation lemma to obtain open neighbourhoods with disjoint closures.
  obtain ⟨U, hxU, hUopen, V, hyV, hVopen, hdisj⟩ :=
    exists_open_nhds_disjoint_closure (x := x) (y := y) hxy
  -- Step 3: Convert the disjointness information into the required equality of intersections.
  have hcl : closure U ∩ closure V = (∅ : Set X) := by
    -- Step 3.1: Show every point in the intersection would contradict disjointness.
    apply Set.eq_empty_of_subset_empty
    intro z hz
    exact (Set.disjoint_left.mp hdisj hz.1 hz.2).elim
  -- Step 4: Package the data into the target existential statement.
  refine ⟨U, V, hUopen, hVopen, hxU, hyV, hcl⟩
