import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Let $f$ be a real uniformly continuous function on the bounded set $E$ in $R^{1}$. Prove that $f$ is bounded on $E$.
-/

/-Informal Proof

Let $a=\inf E$ and $b=\sup E$, and let $\delta>0$ be such that $|f(x)-f(y)|<1$ if $x, y \in E$ and $|x-y|<\delta$. Now choose a positive integer $N$ larger than $(b-a) / \delta$, and consider the $N$ intervals $I_k=\left[a+\frac{k-1}{b-a}, a+\frac{k}{b-a}\right], k=1,2, \ldots, N$. For each $k$ such that $I_k \cap E \neq \varnothing$ let $x_k \in E \cap I_k$. Then let $M=1+\max \left\{\left|f\left(x_k\right)\right|\right\}$. If $x \in E$, we have $\left|x-x_k\right|<\delta$ for some $k$, and hence $|f(x)|<M$.
-/

theorem Rudin_exercise_4_8a
  (E : Set ℝ) (f : ℝ → ℝ) (hf : UniformContinuousOn f E)
  (hE : Bornology.IsBounded E) : Bornology.IsBounded (Set.image f E) := by
  -- Step 1: invoke Heine–Borel to upgrade the boundedness of `E` to compactness of its closure.
  have h_compact : IsCompact (closure E) := by
    -- Step 1.1: `Bornology.IsBounded` on `ℝ` implies the closure is compact.
    simpa using hE.isCompact_closure
  -- Step 2: extract total boundedness information from the compact closure.
  have h_tot_closure : TotallyBounded (closure E) := by
    -- Step 2.1: every compact subset of a uniform space is totally bounded.
    exact h_compact.totallyBounded
  -- Step 2.2: `E` is contained in its closure, hence it is itself totally bounded.
  have h_tot_E : TotallyBounded E := h_tot_closure.subset subset_closure
  -- Step 3: transport total boundedness to the subtype that represents points of `E`.
  have h_tot_subtype :
      TotallyBounded (Set.univ : Set {x : ℝ // x ∈ E}) := by
    -- Step 3.1: describe the image of the subtype coercion and reuse `h_tot_E`.
    have h_image :
        TotallyBounded
          ((Subtype.val : {x : ℝ // x ∈ E} → ℝ) ''
            (Set.univ : Set {x : ℝ // x ∈ E})) := by
      -- Step 3.1.1: the image of `Set.univ` under `Subtype.val` is just `E`.
      simpa [Set.image_univ, Subtype.range_coe_subtype] using h_tot_E
    -- Step 3.2: use uniform inducing of the subtype inclusion to transfer total boundedness.
    exact (totallyBounded_image_iff (isUniformInducing_val E)).1 h_image
  -- Step 4: restrict the function to the subtype so that we can apply uniform-continuity lemmas.
  let g : {x : ℝ // x ∈ E} → ℝ := fun x => f x
  have h_uc : UniformContinuous g := by
    -- Step 4.1: `UniformContinuousOn` is equivalent to uniform continuity of the restriction.
    simpa [g] using (uniformContinuousOn_iff_restrict.mp hf)
  -- Step 5: uniform continuity sends totally bounded sets to totally bounded sets.
  have h_tot_image :
      TotallyBounded
        (g '' (Set.univ : Set {x : ℝ // x ∈ E})) :=
    -- Step 5.1: apply the general `TotallyBounded.image` lemma.
    h_tot_subtype.image h_uc
  -- Step 6: identify the image above with the familiar range/image of `f` on `E`.
  have h_image_univ_eq_range :
      (g '' (Set.univ : Set {x : ℝ // x ∈ E})) = Set.range g := by
    -- Step 6.1: rewrite both sides directly from the definitions.
    ext y
    constructor
    · -- Step 6.1.1: every point in the image gives a witness living in the range.
      intro hy
      rcases hy with ⟨x, -, rfl⟩
      exact ⟨x, rfl⟩
    · -- Step 6.1.2: elements of the range certainly belong to the image of `Set.univ`.
      intro hy
      rcases hy with ⟨x, rfl⟩
      exact ⟨x, Set.mem_univ _, rfl⟩
  -- Step 6.2: relate the range of `g` with the original image `f '' E`.
  have h_range_eq : Set.range g = Set.image f E := by
    -- Step 6.2.1: unpack both sides and compare their witnesses.
    ext y
    constructor
    · -- Step 6.2.1.1: a point in the range corresponds to some element of the subtype.
      intro hy
      rcases hy with ⟨⟨x, hx⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · -- Step 6.2.1.2: any `x ∈ E` provides a corresponding element of the subtype.
      intro hy
      rcases hy with ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  -- Step 7: translate total boundedness of the auxiliary image to `f '' E`.
  have h_tot_final : TotallyBounded (Set.image f E) := by
    -- Step 7.1: first replace `g '' univ` by `Set.range g`, then by `f '' E`.
    have h_tot_range : TotallyBounded (Set.range g) := by
      -- Step 7.1.1: substitute using `h_image_univ_eq_range`.
      simpa [h_image_univ_eq_range] using h_tot_image
    -- Step 7.1.2: now swap `Set.range g` for `f '' E`.
    simpa [h_range_eq] using h_tot_range
  -- Step 8: totally bounded subsets of metric spaces are bounded, which finishes the argument.
  exact h_tot_final.isBounded
