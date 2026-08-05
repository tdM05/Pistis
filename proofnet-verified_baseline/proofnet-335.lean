import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

If $z_1, \ldots, z_n$ are complex, prove that $|z_1 + z_2 + \ldots + z_n| \leq |z_1| + |z_2| + \cdots + |z_n|$.
-/

/-Informal Proof

We can apply the case $n=2$ and induction on $n$ to get
$$
\begin{aligned}
\left|z_1+z_2+\cdots z_n\right| &=\left|\left(z_1+z_2+\cdots+z_{n-1}\right)+z_n\right| \\
& \leq\left|z_1+z_2+\cdots+z_{n-1}\right|+\left|z_n\right| \\
& \leq\left|z_1\right|+\left|z_2\right|+\cdots+\left|z_{n-1}\right|+\left|z_n\right|
\end{aligned}
$$
-/

theorem Rudin_exercise_1_12 (n : ℕ) (f : ℕ → ℂ) :
  ‖∑ i ∈ range n, f i‖ ≤ ∑ i ∈ range n, ‖f i‖ := by
  classical
  -- Step 1: Recall that ℂ is a seminormed additive group, so we can appeal to the
  --         general triangle inequality over finite sums provided by `norm_sum_le`.
  -- Step 2: Apply `norm_sum_le` to the specific finite set `Finset.range n` and the
  --         function `f`, obtaining the desired bound for the partial sum up to `n`.
  -- Step 3: Use `simpa` to recognize that the instantiated inequality is exactly the
  --         target statement.
  simpa using (norm_sum_le (s := Finset.range n) (f := fun i => f i))
