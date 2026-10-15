import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Show that every locally compact Hausdorff space is regular.
-/

/-Informal Proof

Let $X$ be a LCH space.
Then it follows that for every $x \in X$ and for every open neighborhood $U \subseteq X$ of $x$ there exists an open neighborhood $V \subseteq X$ of $x$ such that $\bar{V} \subseteq U$ (and $\bar{V}$ is compact, but this is not important here).
Since $X$ is a Hausdorff space, it satisfies the $T_1$ axiom.
Then it follows that $X$ is regular.
-/

theorem Munkres_exercise_32_3 {X : Type*} [TopologicalSpace X]
  (hX : LocallyCompactSpace X) (hX' : T2Space X) :
  RegularSpace X := by
  -- Step 1: Convert the provided locally compact structure `hX` into a typeclass instance so
  -- Step 1.1: Lean can now treat `X` as weakly locally compact via the global instance
  --           `[LocallyCompactSpace X] → [WeaklyLocallyCompactSpace X]`.
  haveI : LocallyCompactSpace X := hX
  -- Step 2: Convert the Hausdorff (`T₂`) structure `hX'` into an instance; Mathlib then supplies
  -- Step 2.1: the derived `R1Space` structure (`T₂ ⇒ R₁`), which is exactly what we need next.
  haveI : T2Space X := hX'
  -- Step 3: Invoke the Mathlib theorem saying that every weakly locally compact `R₁` space is
  --         regular; Lean applies it automatically once the relevant instances are in scope.
  -- Step 4: Conclude the goal by `inferInstance`, which realizes the regularity of `X`.
  exact inferInstance
