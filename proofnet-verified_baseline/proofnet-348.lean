import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Let $f$ be a continuous real function on a metric space $X$. Let $Z(f)$ (the zero set of $f$ ) be the set of all $p \in X$ at which $f(p)=0$. Prove that $Z(f)$ is closed.
-/

/-Informal Proof

$Z(f)=f^{-1}(\{0\})$, which is the inverse image of a closed set. Hence $Z(f)$ is closed.
-/

theorem Rudin_exercise_4_3
  {α : Type} [MetricSpace α]
  (f : α → ℝ) (h : Continuous f) (z : Set α) (g : z = f⁻¹' {0})
  : IsClosed z := by
  -- Step 1: Recognize that `{0}` is a closed subset of `ℝ`.
  -- Step 1.1: Invoke the general fact that singletons in `ℝ` are closed to justify this.
  have h_zero_closed : IsClosed ({0} : Set ℝ) := by
    -- Step 1.2: `isClosed_singleton` provides the needed closure property for singletons.
    simp
  -- Step 2: Use continuity of `f` to lift the closedness of `{0}` back to the preimage.
  -- Step 2.1: `Continuous.isClosed_preimage` establishes that preimages of closed sets under continuous maps are closed.
  have h_preimage_closed : IsClosed (f ⁻¹' ({0} : Set ℝ)) :=
    -- Step 2.2: Apply the general lemma `IsClosed.preimage` with the previously computed facts.
    IsClosed.preimage h h_zero_closed
  -- Step 3: Rewrite the goal set `z` into `f ⁻¹' {0}` by the provided equality `g`.
  -- Step 3.1: With this rewriting, the previously obtained closedness gives the desired result directly.
  simpa [g] using h_preimage_closed
