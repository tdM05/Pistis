import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that the addition of residue classes $\mathbb{Z}/n\mathbb{Z}$ is associative.
-/

/-Informal Proof

We have
$$
\begin{aligned}
(\bar{a}+\bar{b})+\bar{c} &=\overline{a+b}+\bar{c} \\
&=\overline{(a+b)+c} \\
&=\overline{a+(b+c)} \\
&=\bar{a}+\overline{b+c} \\
&=\bar{a}+(\bar{b}+\bar{c})
\end{aligned}
$$
since integer addition is associative.
-/

theorem Dummit_Foote_exercise_1_1_3 (n : ℕ) : 
  ∀ (x y z : ZMod n), (x + y) + z = x + (y + z) := by
  -- Step 1: Fix arbitrary residue classes `x`, `y`, and `z` in `ZMod n`.
  intro x y z
  -- Step 2: Recall that `(ZMod n)` is an additive semigroup, so `add_assoc` is available.
  -- Step 2.1: Specialize `add_assoc` to the concrete elements `x`, `y`, and `z`.
  have h : (x + y) + z = x + (y + z) := by
    -- Step 2.1.1: Apply the lemma `add_assoc` directly and simplify the goal.
    simpa using (add_assoc x y z)
  -- Step 3: Use the specialized associativity equality as the desired conclusion.
  exact h
