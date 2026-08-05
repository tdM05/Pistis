import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Let $f$ and $g$ be continuous mappings of a metric space $X$ into a metric space $Y$, and let $E$ be a dense subset of $X$. Prove that $f(E)$ is dense in $f(X)$.
-/

/-Informal Proof

To prove that $f(E)$ is dense in $f(X)$, simply use that $f(X)=f(\bar{E}) \subseteq \overline{f(E)}$.
-/

theorem Rudin_exercise_4_4a
  {α : Type} [MetricSpace α]
  {β : Type} [MetricSpace β]
  (f : α → β)
  (s : Set α)
  (h₁ : Continuous f)
  (h₂ : Dense s)
  : f '' Set.univ ⊆ closure (f '' s) := by
  -- Step 1: introduce an arbitrary element of `f '' Set.univ` to prove the needed subset relation.
  intro y hy
  -- Step 2: unravel the membership to pick a witness `x : α` with `f x = y`.
  rcases hy with ⟨x, hx_univ, rfl⟩
  -- Step 3: upgrade `x ∈ Set.univ` to `x ∈ closure s` using the density hypothesis.
  have hx : x ∈ closure s := by
    -- Step 3.1: rewrite `closure s` as `Set.univ` because `h₂` states that `s` is dense.
    convert hx_univ using 1
    -- Step 3.2: simplify with the equality `closure s = Set.univ`.
    simp [h₂.closure_eq]
  -- Step 4: recall the general lemma that continuous maps send `closure s` into `closure (f '' s)`.
  have hsubset : f '' closure s ⊆ closure (f '' s) :=
    image_closure_subset_closure_image (f := f) (s := s) h₁
  -- Step 5: apply the lemma to the witness `(x, hx)` obtained above to finish the proof.
  exact hsubset ⟨x, hx, rfl⟩
