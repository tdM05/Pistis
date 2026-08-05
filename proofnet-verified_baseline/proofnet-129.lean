import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Show that if $X$ is normal, every pair of disjoint closed sets have neighborhoods whose closures are disjoint.
-/

/-Informal Proof

Let $A$ and $B$ be disjoint closed sets. Then there exist disjoint open sets $U$ and $V$ containing $A$ and $B$ respectively.

Since $X \backslash V$ is closed and contains $U$, the closure of $U$ is contained in $X \backslash V$ hence $B$ and closure of $U$ are disjoint.

Repeat steps 1 and 2 for $B$ and $\bar{U}$ instead of $A$ and $B$ respectively and you will have open set $V^{\prime}$ which contains $B$ and its closure doesn't intersect with $\bar{U}$.
-/

theorem Munkres_exercise_31_2 {X : Type*}
  [TopologicalSpace X] [NormalSpace X] {A B : Set X}
  (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
  ∃ (U V : Set X), IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧ closure U ∩ closure V = ∅ := by
  -- Step 1: Switch to classical logic so that choice-based separation lemmas are available.
  classical
  -- Step 2: Use Urysohn's lemma to obtain a continuous function separating `A` and `B`.
  obtain ⟨f, hfA, hfB, hfIcc⟩ := exists_continuous_zero_one_of_isClosed hA hB hAB
  -- Step 3: Define the candidate open neighborhoods as strict sub/super level sets of `f`.
  let U : Set X := {x | f x < (1 : ℝ) / 3}
  let V : Set X := {x | (2 : ℝ) / 3 < f x}
  -- Step 4: Prove that both `U` and `V` are open because they are preimages of open intervals.
  have hUopen : IsOpen U := by
    -- Step 4.1: Apply `isOpen_lt` to the pair `(f, const)` and rewrite the definition of `U`.
    simpa [U] using
      (isOpen_lt f.continuous (continuous_const : Continuous fun _ : X => (1 : ℝ) / 3))
  have hVopen : IsOpen V := by
    -- Step 4.2: Symmetrically, apply `isOpen_lt` to `(const, f)` and rewrite the definition of `V`.
    simpa [V] using
      (isOpen_lt (continuous_const : Continuous fun _ : X => (2 : ℝ) / 3) f.continuous)
  -- Step 5: Show that `A` (resp. `B`) sits inside `U` (resp. `V`) using the boundary values of `f`.
  have hAtoU : A ⊆ U := by
    -- Step 5.1: `f` vanishes on `A`, hence every point of `A` witnesses `f x < 1/3`.
    intro x hx
    have hx0 : f x = 0 := by simpa using hfA hx
    change f x < (1 : ℝ) / 3
    calc
      f x = 0 := hx0
      _ < (1 : ℝ) / 3 := by norm_num
  have hBtoV : B ⊆ V := by
    -- Step 5.2: `f` equals `1` on `B`, so each point of `B` satisfies `(2/3) < f x`.
    intro x hx
    have hx1 : f x = 1 := by simpa using hfB hx
    have : (2 : ℝ) / 3 < (1 : ℝ) := by norm_num
    simpa [V, hx1] using this
  -- Step 6: Introduce closed supersets controlling the closures of `U` and `V`.
  let Ule : Set X := {x | f x ≤ (1 : ℝ) / 3}
  let Vge : Set X := {x | (2 : ℝ) / 3 ≤ f x}
  -- Step 6.1: Record that these supersets are closed as preimages of closed intervals.
  have hUleClosed : IsClosed Ule := by
    simpa [Ule] using
      (isClosed_le f.continuous (continuous_const : Continuous fun _ : X => (1 : ℝ) / 3))
  have hVgeClosed : IsClosed Vge := by
    simpa [Vge] using
      (isClosed_le (continuous_const : Continuous fun _ : X => (2 : ℝ) / 3) f.continuous)
  -- Step 6.2: Note that `U ⊆ Ule` and `V ⊆ Vge`, so their closures remain inside the closed supersets.
  have hUSubUle : U ⊆ Ule := by
    intro x hx
    have hxlt : f x < (1 : ℝ) / 3 := by simpa [U] using hx
    have : f x ≤ (1 : ℝ) / 3 := le_of_lt hxlt
    simpa [Ule] using this
  have hVSubVge : V ⊆ Vge := by
    intro x hx
    have hxgt : (2 : ℝ) / 3 < f x := by simpa [V] using hx
    have : (2 : ℝ) / 3 ≤ f x := le_of_lt hxgt
    simpa [Vge] using this
  have hclosureUsubset : closure U ⊆ Ule :=
    (IsClosed.closure_subset_iff hUleClosed).2 hUSubUle
  have hclosureVsubset : closure V ⊆ Vge :=
    (IsClosed.closure_subset_iff hVgeClosed).2 hVSubVge
  -- Step 7: Use the previous containments to prove that the closures are disjoint.
  have hsubset_empty : closure U ∩ closure V ⊆ (∅ : Set X) := by
    -- Step 7.1: A point in the intersection would give incompatible inequalities for `f x`.
    intro x hx
    rcases hx with ⟨hxU, hxV⟩
    have hxle : f x ≤ (1 : ℝ) / 3 := by
      have := hclosureUsubset hxU
      simpa [Ule] using this
    have hxge : (2 : ℝ) / 3 ≤ f x := by
      have := hclosureVsubset hxV
      simpa [Vge] using this
    have hcontr : (2 : ℝ) / 3 ≤ (1 : ℝ) / 3 := le_trans hxge hxle
    have : (2 : ℝ) / 3 < (2 : ℝ) / 3 :=
      lt_of_le_of_lt hcontr (by norm_num : (1 : ℝ) / 3 < (2 : ℝ) / 3)
    exact (lt_irrefl ((2 : ℝ) / 3)) this
  have hclosureEq : closure U ∩ closure V = (∅ : Set X) :=
    Set.Subset.antisymm hsubset_empty (by intro x hx; cases hx)
  -- Step 8: Assemble the data to finish the separation statement with disjoint closures.
  refine ⟨U, V, hUopen, hVopen, hAtoU, hBtoV, hclosureEq⟩
