import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Let $f$ and $g$ be continuous mappings of a metric space $X$ into a metric space $Y$, and let $P$ be a dense subset of $X$. Prove that if $g(p) = f(p)$ for all $p \in P$ then $g(p) = f(p)$ for all $p \in X$.
-/

/-Informal Proof

The function $\varphi: X \rightarrow R^1$ given by
$$
\varphi(p)=d_Y(f(p), g(p))
$$
is continuous, since
$$
\left|d_Y(f(p), g(p))-d_Y(f(q), g(q))\right| \leq d_Y(f(p), f(q))+d_Y(g(p), g(q))
$$
(This inequality follows from the triangle inequality, since
$$
d_Y(f(p), g(p)) \leq d_Y(f(p), f(q))+d_Y(f(q), g(q))+d_Y(g(q), g(p)),
$$
and the same inequality holds with $p$ and $q$ interchanged. The absolute value $\left|d_Y(f(p), g(p))-d_Y(f(q), g(q))\right|$ must be either $d_Y(f(p), g(p))-d_Y(f(q), g(q))$ or $d_Y(f(q), g(q))-d_Y(f(p), g(p))$, and the triangle inequality shows that both of these numbers are at most $d_Y(f(p), f(q))+d_Y(g(p), g(q))$.)
By the previous problem, the zero set of $\varphi$ is closed. But by definition
$$
Z(\varphi)=\{p: f(p)=g(p)\} .
$$
Hence the set of $p$ for which $f(p)=g(p)$ is closed. Since by hypothesis it is dense, it must be $X$.
-/

theorem Rudin_exercise_4_4b
  {α : Type} [MetricSpace α]
  {β : Type} [MetricSpace β]
  (f g : α → β)
  (s : Set α)
  (h₁ : Continuous f)
  (h₂ : Continuous g)
  (h₃ : Dense s)
  (h₄ : ∀ x ∈ s, f x = g x)
  : f = g := by
  -- Step 1: Consider the agreement set {x | f x = g x} and record that it is closed.
  have h_closed : IsClosed {x : α | f x = g x} := by
    -- Step 1.1: The equality set of two continuous functions is closed via `isClosed_eq`.
    simpa using isClosed_eq h₁ h₂
  -- Step 2: Translate the hypothesis h₄ into the statement that s is contained in the agreement set.
  have hs_subset : s ⊆ {x : α | f x = g x} := by
    -- Step 2.1: For any x ∈ s, the assumption h₄ tells us f x = g x.
    intro x hx
    exact h₄ x hx
  -- Step 3: Use density of s to force the agreement set to contain the whole space.
  have hs_closure : closure s = (Set.univ : Set α) := h₃.closure_eq
  -- Step 3.1: Since the agreement set is closed and contains s, it also contains closure s.
  have hclosure_subset : closure s ⊆ {x : α | f x = g x} :=
    closure_minimal hs_subset h_closed
  -- Step 3.2: Replace closure s with the whole space via density to deduce univ ⊆ agreement set.
  have huniv_subset : (Set.univ : Set α) ⊆ {x : α | f x = g x} := by
    simpa [hs_closure] using hclosure_subset
  -- Step 4: Convert set-containment information into pointwise equality and conclude with function extensionality.
  apply funext
  intro x
  -- Step 4.1: Any point x lies in univ, hence in the agreement set, yielding f x = g x.
  have hx : x ∈ {y : α | f y = g y} := huniv_subset (Set.mem_univ x)
  -- Step 4.2: Interpret membership in the agreement set as the desired equality.
  simpa using hx
