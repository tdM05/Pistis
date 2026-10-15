import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Let $X$ be a topological space and let $Y$ be a metric space. Let $f_{n}: X \rightarrow Y$ be a sequence of continuous functions. Let $x_{n}$ be a sequence of points of $X$ converging to $x$. Show that if the sequence $\left(f_{n}\right)$ converges uniformly to $f$, then $\left(f_{n}\left(x_{n}\right)\right)$ converges to $f(x)$.
-/

/-Informal Proof

Let $d$ be the metric on $Y$. Let $V$ be a neighbourhood of $f(x)$, and let $\varepsilon>0$ be such that $f(x) \in B_d(f(x), \varepsilon) \subset V$. Since $\left(f_n\right)_n$ converges uniformly to $f$, there exists $N_1 \in \mathbb{Z}_{+}$such that $d\left(f_n(x), f(x)\right)<\varepsilon / 2$ for all $x \in X$ and all $n \geq N_1$, so that $d\left(f_n\left(x_n\right), f\left(x_n\right)\right)<\varepsilon / 2$ for all $n \geq N_1$. Moreover, $f$ is continuous, so there exists $N_2 \in \mathbb{Z}_{+}$such that $d\left(f\left(x_n\right), f(x)\right)<\varepsilon / 2$ for all $n \geq N_2$. Thus, if $N>\max \left\{N_1, N_2\right\}$, then
$$
d\left(f_n\left(x_n\right), f(x)\right) \leq d\left(f_n\left(x_n\right), f\left(x_n\right)\right)+d\left(f\left(x_n\right), f(x)\right)<\frac{\varepsilon}{2}+\frac{\varepsilon}{2}=\varepsilon
$$
for all $n \geq N$, so $f_n\left(x_n\right) \in V$ for all $n \geq N$. It follows that $\left(f_n\left(x_n\right)\right)_n$ converges to $f(x)$.
-/

theorem Munkres_exercise_21_8
  {X : Type*} [TopologicalSpace X] {Y : Type*} [MetricSpace Y]
  {f : ℕ → X → Y} {x : ℕ → X}
  (hf : ∀ n, Continuous (f n))
  (x₀ : X)
  (hx : Tendsto x atTop (𝓝 x₀))
  (f₀ : X → Y)
  (hh : TendstoUniformly f f₀ atTop) :
  Tendsto (λ n => f n (x n)) atTop (𝓝 (f₀ x₀)) := by
  classical
  -- Step 1: Convert the uniform convergence hypothesis into continuity data for `f₀`.
  -- Step 1.1: Record that the family `(f n)` is eventually continuous (indeed, always continuous).
  have h_eventually_cont : ∀ᶠ n in atTop, Continuous (f n) :=
    -- Step 1.1.1: Use `Filter.eventually_atTop.2` with the universal witness coming from `hf`.
    Filter.eventually_atTop.2 (by
      refine ⟨0, ?_⟩
      -- Step 1.1.1.1: For any `n ≥ 0`, `hf n` supplies the desired continuity.
      intro n _
      exact hf n)
  -- Step 1.2: Apply `TendstoUniformly.continuous` to deduce that the limit function `f₀` is continuous.
  have hf₀_continuous : Continuous f₀ :=
    hh.continuous h_eventually_cont.frequently
  -- Step 2: Specialize the continuity of `f₀` to obtain continuity at the specific point `x₀`.
  have hf₀_cont_at : ContinuousAt f₀ x₀ :=
    hf₀_continuous.continuousAt
  -- Step 3: Invoke the uniform convergence composition lemma together with the convergence of `(x n)` towards `x₀`.
  -- Step 3.1: Apply `TendstoUniformly.tendsto_comp` to combine the preceding steps and conclude.
  exact hh.tendsto_comp hf₀_cont_at hx
