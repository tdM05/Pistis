import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Let $Y$ be an ordered set in the order topology. Let $f, g: X \rightarrow Y$ be continuous. Let $h: X \rightarrow Y$ be the function $h(x)=\min \{f(x), g(x)\}.$ Show that $h$ is continuous.
-/

/-Informal Proof

Let $A=\{x \mid f(x) \leq g(x)\}$ and $B=\{x \mid g(x) \leq f(x)\}$. Then $A$ and $B$ are closed in $X$ by (a), $A \cap B=\{x \mid f(x)=g(x)\}$, and $X=A \cup B$. Since $f$ and $g$ are continuous, their restrictions $f^{\prime}: A \rightarrow Y$ and $g^{\prime}: B \rightarrow Y$ are continuous. It follows from the pasting lemma that
$$
h: X \rightarrow Y, \quad h(x)=\min \{f(x), g(x)\}= \begin{cases}f^{\prime}(x) & \text { if } x \in A \\ g^{\prime}(x) & \text { if } x \in B\end{cases}
$$
is continuous
-/

theorem Munkres_exercise_18_8b {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [LinearOrder Y] [OrderTopology Y] {f g : X → Y}
  (hf : Continuous f) (hg : Continuous g) :
  Continuous (λ x => min (f x) (g x)) := by
  -- Step 1: Enable classical choice so that pointwise minimums reduce to classical lemmas.
  classical
  -- Step 2: Apply the mathlib lemma stating that the pointwise minimum of two continuous maps is continuous.
  -- Step 2.1: The lemma `hf.min hg` upgrades the continuity of `f` and `g` to the continuity of `fun x => min (f x) (g x)`.
  -- Step 2.2: The goal matches the conclusion of `hf.min hg`, so we close the proof by rewriting with `simpa`.
  simpa using hf.min hg
