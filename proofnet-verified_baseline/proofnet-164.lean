import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

If $f$ is a continuous mapping of a metric space $X$ into a metric space $Y$, prove that $f(\overline{E}) \subset \overline{f(E)}$ for every set $E \subset X$. ($\overline{E}$ denotes the closure of $E$).
-/

/-Informal Proof

Let $x \in \bar{E}$. We need to show that $f(x) \in \overline{f(E)}$. To this end, let $O$ be any neighborhood of $f(x)$. Since $f$ is continuous, $f^{-1}(O)$ contains (is) a neighborhood of $x$. Since $x \in \bar{E}$, there is a point $u$ of $E$ in $f^{-1}(O)$. Hence $\frac{f(u)}{f(E)} \in O \cap f(E)$. Since $O$ was any neighborhood of $f(x)$, it follows that $f(x) \in \overline{f(E)}$
-/

theorem Rudin_exercise_4_2a
  {α : Type} [MetricSpace α]
  {β : Type} [MetricSpace β]
  (f : α → β)
  (h₁ : Continuous f)
  : ∀ (x : Set α), f '' (closure x) ⊆ closure (f '' x) := by
  -- Step 1: Switch to classical logic so that set-membership simplifications can freely use choice.
  classical
  -- Step 2: Fix an arbitrary subset `x : Set α`; the remaining goal is the desired subset inclusion.
  intro x
  -- Step 3: Apply the general mathlib lemma stating that continuous maps send closures into closures.
  -- Step 3.1: The lemma `image_closure_subset_closure_image` exactly states `f '' closure x ⊆ closure (f '' x)`.
  -- Step 3.2: Specialize this lemma to our map `f` and set `x`, finishing the proof immediately.
  simpa using image_closure_subset_closure_image (f := f) (s := x) h₁
