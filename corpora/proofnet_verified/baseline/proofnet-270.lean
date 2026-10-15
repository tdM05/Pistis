import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

If $a^2 = 0$ in $R$, show that $ax + xa$ commutes with $a$.
-/

/-Informal Proof

We need to show that
$$
a(a x+x a)=(a x+x a) a \text { for } a, x \in R .
$$
Now,
$$
\begin{gathered}
a(a x+x a)=a(a x)+a(x a) \\
=a^2 x+a x a \\
=0+a x a=a x a .
\end{gathered}
$$
Again,
$$
\begin{gathered}
(a x+x a) a=(a x) a+(x a) a \\
=a x a+x a^2 \\
=a x a+0=a x a .
\end{gathered}
$$
It follows that,
$$
a(a x+x a)=(a x+x a) a, \text { for } x, a \in R .
$$
This shows that $a x+x a$ commutes with $a$. This completes the proof.
-/

theorem Herstein_exercise_4_2_6 {R : Type*} [Ring R] (a x : R)
  (h : a ^ 2 = 0) : a * (a * x + x * a) = (a * x + x * a) * a := by
  -- Step 1: Rewrite the squared hypothesis so we can substitute it into products later.
  have h_mul_sq : a * a = 0 := by
    -- Step 1.1: Use the identity `a ^ 2 = a * a` (lemma `pow_two`) to translate the assumption.
    simpa [pow_two] using h
  -- Step 2: Expand the left-hand side using distributivity and associativity so only triple products remain.
  have h_left : a * (a * x + x * a) = a * x * a := by
    -- Step 2.1: Apply left distributivity of multiplication over addition.
    calc
      a * (a * x + x * a)
          = a * (a * x) + a * (x * a) := by
            -- Step 2.1.1: Direct application of `mul_add`.
            simp [mul_add]
      _ = (a * a) * x + a * (x * a) := by
            -- Step 2.2: Reassociate the first summand via associativity.
            simp [mul_assoc]
      _ = (a * a) * x + (a * x) * a := by
            -- Step 2.3: Reassociate the second summand.
            simp [mul_assoc]
      _ = 0 * x + (a * x) * a := by
            -- Step 2.4: Substitute `a * a = 0` from Step 1.
            simp [h_mul_sq]
      _ = (0 : R) + (a * x) * a := by
            -- Step 2.5: Recognize multiplication by zero.
            simp
      _ = a * x * a := by
            -- Step 2.6: Drop the leading zero and read `(a * x) * a` as `a * x * a`.
            simp [zero_add]
  -- Step 3: Expand the right-hand side analogously and reduce it to the same triple product.
  have h_right : (a * x + x * a) * a = a * x * a := by
    -- Step 3.1: Apply right distributivity of multiplication over addition.
    calc
      (a * x + x * a) * a
          = (a * x) * a + (x * a) * a := by
            -- Step 3.1.1: Direct application of `add_mul`.
            simp [add_mul]
      _ = (a * x) * a + x * (a * a) := by
            -- Step 3.2: Reassociate the second summand.
            simp [mul_assoc]
      _ = (a * x) * a + x * 0 := by
            -- Step 3.3: Substitute `a * a = 0` using Step 1.
            simp [h_mul_sq]
      _ = (a * x) * a + 0 := by
            -- Step 3.4: Recognize multiplication by zero.
            simp
      _ = a * x * a := by
            -- Step 3.5: Remove the trailing zero and rewrite `(a * x) * a` via associativity notation.
            simp [add_zero]
  -- Step 4: Combine the two reductions to conclude that the two sides are equal.
  calc
    a * (a * x + x * a)
        = a * x * a := h_left
    _ = (a * x + x * a) * a := h_right.symm
