import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that the multiplication of residue class $\mathbb{Z}/n\mathbb{Z}$ is associative.
-/

/-Informal Proof

We have
$$
\begin{aligned}
(\bar{a} \cdot \bar{b}) \cdot \bar{c} &=\overline{a \cdot b} \cdot \bar{c} \\
&=\overline{(a \cdot b) \cdot c} \\
&=\overline{a \cdot(b \cdot c)} \\
&=\bar{a} \cdot \overline{b \cdot c} \\
&=\bar{a} \cdot(\bar{b} \cdot \bar{c})
\end{aligned}
$$
since integer multiplication is associative.
-/

theorem Dummit_Foote_exercise_1_1_4 (n : ℕ) (a b c : ZMod n) :
  (a * b) * c = a * (b * c) := by
  -- Step 1: Observe that `ZMod n` carries the usual semiring structure inherited
  -- from the integers modulo `n`, so multiplication behaves exactly like the
  -- integer product followed by reduction modulo `n`.
  -- Step 1.1: Under this semiring structure Lean already provides `mul_assoc`,
  -- the lemma expressing associativity of multiplication for any three elements.
  -- Step 2: Apply this associativity lemma to the specific triple `(a, b, c)` to
  -- rewrite `(a * b) * c` as `a * (b * c)`.
  -- Step 3: Use `simp` with the associativity lemma to close the goal, since the
  -- simplifier rewrites the left-associated product into the right-associated one.
  simp [mul_assoc]
