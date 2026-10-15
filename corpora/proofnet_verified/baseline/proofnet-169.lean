import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

A uniformly continuous function of a uniformly continuous function is uniformly continuous.
-/

/-Informal Proof

Let $f: X \rightarrow Y$ and $g: Y \rightarrow Z$ be uniformly continuous. Then $g \circ f: X \rightarrow Z$ is uniformly continuous, where $g \circ f(x)=g(f(x))$ for all $x \in X$.
To prove this fact, let $\varepsilon>0$ be given. Then, since $g$ is uniformly continuous, there exists $\eta>0$ such that $d_Z(g(u), g(v))<\varepsilon$ if $d_Y(u, v)<\eta$. Since $f$ is uniformly continuous, there exists $\delta>0$ such that $d_Y(f(x), f(y))<\eta$ if $d_X(x, y)<\delta$

It is then obvious that $d_Z(g(f(x)), g(f(y)))<\varepsilon$ if $d_X(x, y)<\delta$, so that $g \circ f$ is uniformly continuous.
-/

theorem Rudin_exercise_4_12
  {α β γ : Type*} [UniformSpace α] [UniformSpace β] [UniformSpace γ]
  {f : α → β} {g : β → γ}
  (hf : UniformContinuous f) (hg : UniformContinuous g) :
  UniformContinuous (g ∘ f) := by
  -- Step 1: Recall the library lemma `UniformContinuous.comp` which certifies that
  --         composing a uniformly continuous function on the left with another one
  --         yields a uniformly continuous composite.
  -- Step 1.1: In our situation the "outer" function is `g`, so we plan to feed `hg`
  --           into this lemma.
  -- Step 1.2: The "inner" function is `f`, so we supply `hf` for the remaining hypothesis.
  -- Step 2: Invoke the lemma with these two hypotheses, which produces the desired conclusion.
  exact hg.comp hf
