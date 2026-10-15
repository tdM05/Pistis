import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that $(a_1a_2\dots a_n)^{-1} = a_n^{-1}a_{n-1}^{-1}\dots a_1^{-1}$ for all $a_1, a_2, \dots, a_n\in G$.
-/

/-Informal Proof

For $n=1$, note that for all $a_1 \in G$ we have $a_1^{-1}=a_1^{-1}$.
Now for $n \geq 2$ we proceed by induction on $n$. For the base case, note that for all $a_1, a_2 \in G$ we have
$$
\left(a_1 \cdot a_2\right)^{-1}=a_2^{-1} \cdot a_1^{-1}
$$
since
$$
a_1 \cdot a_2 \cdot a_2^{-1} a_1^{-1}=1 .
$$
For the inductive step, suppose that for some $n \geq 2$, for all $a_i \in G$ we have
$$
\left(a_1 \cdot \ldots \cdot a_n\right)^{-1}=a_n^{-1} \cdot \ldots \cdot a_1^{-1} .
$$
Then given some $a_{n+1} \in G$, we have
$$
\begin{aligned}
\left(a_1 \cdot \ldots \cdot a_n \cdot a_{n+1}\right)^{-1} &=\left(\left(a_1 \cdot \ldots \cdot a_n\right) \cdot a_{n+1}\right)^{-1} \\
&=a_{n+1}^{-1} \cdot\left(a_1 \cdot \ldots \cdot a_n\right)^{-1} \\
&=a_{n+1}^{-1} \cdot a_n^{-1} \cdot \ldots \cdot a_1^{-1},
\end{aligned}
$$
using associativity and the base case where necessary.
-/

theorem Dummit_Foote_exercise_1_1_15 {G : Type*} [Group G] (as : List G) :
  as.prod⁻¹ = (as.reverse.map (λ x => x⁻¹)).prod := by
  -- Step 1: We carry out induction on the structure of the list `as`.
  induction as with
  | nil =>
      -- Step 1.1: When `as = []`, both sides are the inverse of `1`, so they simplify to `1`.
      --           The Lean `simp` tactic evaluates `List.prod` and `List.reverse` on `[]` automatically.
      simp
  | cons a as ih =>
      -- Step 2: Assume the statement holds for the tail `as` and prove it for `a :: as`.
      -- Step 2.1: Expand the left-hand side using the definition of `List.prod` on a cons.
      -- Step 2.2: Expand and rearrange the right-hand side using `reverse_cons`, `map_append`, and `prod_append`.
      -- Step 2.3: Substitute the inductive hypothesis `ih` for the tail and use the group identity `(xy)⁻¹ = y⁻¹ x⁻¹`.
      -- Step 2.4: Simplify the remaining expression to conclude the equality for `a :: as`.
      simp [List.reverse_cons, List.map_append, List.prod_append, List.prod_cons, ih]
