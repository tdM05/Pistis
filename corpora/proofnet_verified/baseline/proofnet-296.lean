import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Let $Y$ be an ordered set in the order topology. Let $f, g: X \rightarrow Y$ be continuous. Show that the set $\{x \mid f(x) \leq g(x)\}$ is closed in $X$.
-/

/-Informal Proof

We prove that $U=\{x \mid g(x)<f(x)\}$ is open in $X$. Let $a \in U$, so that $g(a)<f(a)$. If there is an element $c$ between $g(a)$ and $f(a)$, then $a \in g^{-1}((-\infty, c)) \cap f^{-1}((c,+\infty))$. If there are no elements between $g(a)$ and $f(a)$, then $a \in g^{-1}\left((-\infty, f(a)) \cap f^{-1}((g(a),+\infty))\right.$. Note that all these preimages are open since $f$ and $g$ are continuous. Thus $U=V \cup W$, where
$$
V=\bigcup_{c \in X} g^{-1}((-\infty, c)) \cap f^{-1}((c,+\infty)) \quad \text { and } \quad W=\bigcup_{\substack{g(a)<f(a) \\(g(a), f(a))=\emptyset}} g^{-1}\left((-\infty, f(a)) \cap f^{-1}((g(a),+\infty))\right.
$$
are open in $X$. So $U$ is open in $X$ and therefore $X \backslash U=\{x \mid f(x) \leq g(x)\}$ is closed in $X$.
-/

theorem Munkres_exercise_18_8a {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [LinearOrder Y] [OrderTopology Y] {f g : X → Y}
  (hf : Continuous f) (hg : Continuous g) :
  IsClosed {x | f x ≤ g x} := by
  -- Step 1: Invoke the general Mathlib fact `isClosed_le`, which states that the
  --         set `{x | f x ≤ g x}` is closed once both functions are continuous.
  -- Step 1.1: Hypothesis `hf` provides the required continuity of `f`.
  -- Step 1.2: Hypothesis `hg` provides the required continuity of `g`.
  -- Step 2: Specializing `isClosed_le` with `hf` and `hg` yields exactly the
  --         desired closedness, so we simply rewrite the goal to conclude.
  simpa using isClosed_le hf hg
