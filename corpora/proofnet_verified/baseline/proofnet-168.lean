import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Let f be a real uniformly continuous function on the bounded set E in $R^{1}$. Prove that f is bounded on E.
-/

/-Informal Proof

Since $E$ is bounded in $\mathbb{R}$, it is totally bounded. A uniformly continuous function maps totally bounded sets to totally bounded sets. In $\mathbb{R}$, totally bounded sets are bounded, so $f(E)$ is bounded.
-/

theorem Rudin_exercise_4_8a
  (E : Set ℝ) (h : Bornology.IsBounded E) :
  ∃ f : ℝ → ℝ, UniformContinuousOn f E ∧ ¬ Bornology.IsBounded (Set.image f E) := by
  sorry

/-
The informal argument forgets that bounded subsets of `ℝ` are totally bounded, and uniformly
continuous maps send totally bounded sets to totally bounded (hence bounded) sets. Therefore no
uniformly continuous function can be unbounded on a bounded subset of `ℝ`, so the original claim
is false.
-/

lemma bounded_image_of_uniformContinuousOn
    (E : Set ℝ) (hE : Bornology.IsBounded E)
    (f : ℝ → ℝ) (hf : UniformContinuousOn f E) :
    Bornology.IsBounded (Set.image f E) := by
  -- Step 1: upgrade the boundedness of `E` to compactness of `closure E` via Heine–Borel.
  have h_compact : IsCompact (closure E) :=
    -- Step 1.1: invoke the `isCompact_closure` lemma specialized to bounded subsets of `ℝ`.
    hE.isCompact_closure
  -- Step 2: deduce that `closure E` (and hence `E`) is totally bounded.
  have h_tot_closure : TotallyBounded (closure E) :=
    -- Step 2.1: compact sets are totally bounded.
    h_compact.totallyBounded
  -- Step 2.2: `E` is a subset of its closure, so `E` itself is totally bounded.
  have h_tot_E : TotallyBounded E :=
    h_tot_closure.subset subset_closure
  -- Step 3: transfer total boundedness to the subtype `(Subtype E)` so that we can talk about
  -- `UniformContinuous` functions defined on the restricted domain.
  have h_tot_subtype :
      TotallyBounded (Set.univ : Set {x : ℝ // x ∈ E}) := by
    -- Step 3.1: rewrite the image of the subtype inclusion as the original set `E`.
    have h_tot_image :
        TotallyBounded
          ((Subtype.val : {x : ℝ // x ∈ E} → ℝ) '' (Set.univ : Set {x : ℝ // x ∈ E})) := by
      -- Step 3.1.1: the image of `Set.univ` under `Subtype.val` is literally `E`.
      simpa [Set.image_univ, Subtype.range_coe_subtype] using h_tot_E
    -- Step 3.2: use the uniform inducing property of the subtype inclusion.
    exact (totallyBounded_image_iff (isUniformInducing_val E)).1 h_tot_image
  -- Step 4: reinterpret uniform continuity on `E` as uniform continuity of the restricted map.
  let g : {x : ℝ // x ∈ E} → ℝ := fun x => f x
  have h_restrict : UniformContinuous g := by
    -- Step 4.1: the helper lemma translates `UniformContinuousOn` to the restricted function.
    simpa [g] using (uniformContinuousOn_iff_restrict.mp hf)
  -- Step 5: apply the general result that uniform continuity preserves total boundedness.
  have h_tot_image :
      TotallyBounded
        (g '' (Set.univ : Set {x : ℝ // x ∈ E})) :=
    h_tot_subtype.image h_restrict
  -- Step 6: rewrite the range of the restricted map `g` as the familiar image `f '' E`.
  have h_range_eq : Set.range g = Set.image f E := by
    -- Step 6.1: unpack the range predicate and compare witnesses.
    ext y
    constructor
    · -- Step 6.1.1: a point in the range comes from some subtype element.
      intro hy
      rcases hy with ⟨⟨x, hxE⟩, rfl⟩
      exact ⟨x, hxE, rfl⟩
    · -- Step 6.1.2: any `y = f x` with `x ∈ E` yields a range witness.
      intro hy
      rcases hy with ⟨x, hxE, rfl⟩
      exact ⟨⟨x, hxE⟩, rfl⟩
  -- Step 6.2: also relate the auxiliary image `g '' univ` to that range.
  have h_image_univ_eq_range :
      (g '' (Set.univ : Set {x : ℝ // x ∈ E})) = Set.range g := by
    -- Step 6.2.1: elements on the left are obtained by evaluating `g`.
    ext y
    constructor
    · -- Step 6.2.1.1: start from the image description.
      intro hy
      rcases hy with ⟨x, -, rfl⟩
      exact ⟨x, rfl⟩
    · -- Step 6.2.1.2: points in the range obviously belong to the image of `univ`.
      intro hy
      rcases hy with ⟨x, rfl⟩
      exact ⟨x, Set.mem_univ _, rfl⟩
  -- Step 7: convert the previous result to a statement about the range.
  have h_tot_range : TotallyBounded (Set.range g) := by
    -- Step 7.1: use Step 6.2 to replace the auxiliary image with the range.
    simpa [h_image_univ_eq_range] using h_tot_image
  -- Step 7.2: transport total boundedness from the range to `f '' E`.
  have h_tot_final : TotallyBounded (Set.image f E) := by
    simpa [h_range_eq] using h_tot_range
  -- Step 7.3: totally bounded subsets of a metric space are bounded.
  exact h_tot_final.isBounded

/-
Corrected statement: whenever `E ⊆ ℝ` is bounded, **every** function that is uniformly continuous
on `E` must be bounded on `E`; equivalently, no counterexample function can exist.
-/

theorem Rudin_exercise_4_8a_neg
  (E : Set ℝ) (h : Bornology.IsBounded E) :
  ¬ ∃ f : ℝ → ℝ, UniformContinuousOn f E ∧ ¬ Bornology.IsBounded (Set.image f E) := by
  -- Step 1: assume (for contradiction) that such a function `f` exists.
  rintro ⟨f, hfUC, hf_unbounded⟩
  -- Step 2: show that `f '' E` must actually be bounded by invoking the helper lemma.
  have h_bounded : Bornology.IsBounded (Set.image f E) :=
    bounded_image_of_uniformContinuousOn E h f hfUC
  -- Step 3: contradict the assumed unboundedness of the image.
  exact hf_unbounded h_bounded

theorem Rudin_exercise_4_8a_corrected
  (E : Set ℝ) (h : Bornology.IsBounded E) :
  ∀ f : ℝ → ℝ, UniformContinuousOn f E → Bornology.IsBounded (Set.image f E) := by
  -- Step 1: introduce an arbitrary uniformly continuous function on `E`.
  intro f hf
  -- Step 2: apply the previously established lemma to obtain boundedness.
  exact bounded_image_of_uniformContinuousOn E h f hf
