import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Suppose $f$ is a uniformly continuous mapping of a metric space $X$ into a metric space $Y$ and prove that $\left\{f\left(x_{n}\right)\right\}$ is a Cauchy sequence in $Y$ for every Cauchy sequence $\{x_n\}$ in $X$.
-/

/-Informal Proof

Suppose $\left\{x_n\right\}$ is a Cauchy sequence in $X$. Let $\varepsilon>0$ be given. Let $\delta>0$ be such that $d_Y(f(x), f(u))<\varepsilon$ if $d_X(x, u)<\delta$. Then choose $N$ so that $d_X\left(x_n, x_m\right)<\delta$ if $n, m>N$. Obviously $d_Y\left(f\left(x_n\right), f\left(x_m\right)\right)<\varepsilon$ if $m, n>N$, showing that $\left\{f\left(x_n\right)\right\}$ is a Cauchy sequence.
-/

theorem Rudin_exercise_4_11a
  {X : Type*} [MetricSpace X]
  {Y : Type*} [MetricSpace Y]
  (f : X → Y) (hf : UniformContinuous f)
  (x : ℕ → X) (hx : CauchySeq x) :
  CauchySeq (λ n => f (x n)) := by
  -- Step 1: Produce the Cauchy property for `f ∘ x` using uniform continuity.
  have hcomp : CauchySeq (f ∘ x) := by
    -- Step 1.1: Directly apply `UniformContinuous.comp_cauchySeq` to `hf` and `hx`.
    --          This lemma says a uniformly continuous map sends Cauchy sequences to Cauchy sequences.
    simpa using hf.comp_cauchySeq hx
  -- Step 2: Reinterpret the previous result in the requested form `λ n => f (x n)`.
  -- Step 2.1: The expression `f ∘ x` is definitionally equal to `λ n => f (x n)`,
  --           so we conclude by rewriting with `Function.comp`.
  simpa [Function.comp] using hcomp
