import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators



/-Informal Statement

Prove that if $a \in \mathbf{F}$, $v \in V$, and $av = 0$, then $a = 0$ or $v = 0$.
-/

/-Informal Proof

If $a=0$, then we immediately have our result. So suppose $a \neq 0$. Then, because $a$ is some nonzero real or complex number, it has a multiplicative inverse $\frac{1}{a}$. Now suppose that $v$ is some vector such that
$$
a v=0
$$
Multiply by $\frac{1}{a}$ on both sides of this equation to get
$$
\begin{aligned}
\frac{1}{a}(a v) & =\frac{1}{a} 0 & & \\
\frac{1}{a}(a v) & =0 & & \\
\left(\frac{1}{a} \cdot a\right) v & =0 & & \text { (associativity) } \\
1 v & =0 & & \text { (definition of } 1/a) \\
v & =0 & & \text { (multiplicative identity) }
\end{aligned}
$$
Hence either $a=0$ or, if $a \neq 0$, then $v=0$.
-/

theorem Axler_exercise_1_4 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] (v : V) (a : F): a • v = 0 → a = 0 ∨ v = 0 := by
  -- Step 1: Introduce the hypothesis `a • v = 0` so we can reason with it directly.
  intro h
  -- Step 2: Interpret the equality `a • v = 0` via the lemma `smul_eq_zero` that holds over fields.
  have hDisj : a = 0 ∨ v = 0 := by
    -- Step 2.1: Apply `smul_eq_zero.mp` to translate the equality into the desired disjunction.
    simpa using (smul_eq_zero.mp h)
  -- Step 3: Output the disjunction computed in Step 2 to prove the goal.
  exact hDisj
