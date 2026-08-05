import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

For $x$ an element in $G$ show that $x$ and $x^{-1}$ have the same order.
-/

/-Informal Proof

Recall that the order of a group element is either a positive integer or infinity.
Suppose $|x|$ is infinite and that $\left|x^{-1}\right|=n$ for some $n$. Then
$$
x^n=x^{(-1) \cdot n \cdot(-1)}=\left(\left(x^{-1}\right)^n\right)^{-1}=1^{-1}=1,
$$
a contradiction. So if $|x|$ is infinite, $\left|x^{-1}\right|$ must also be infinite. Likewise, if $\left|x^{-1}\right|$ is infinite, then $\left|\left(x^{-1}\right)^{-1}\right|=|x|$ is also infinite.
Suppose now that $|x|=n$ and $\left|x^{-1}\right|=m$ are both finite. Then we have
$$
\left(x^{-1}\right)^n=\left(x^n\right)^{-1}=1^{-1}=1,
$$
so that $m \leq n$. Likewise, $n \leq m$. Hence $m=n$ and $x$ and $x^{-1}$ have the same order.
-/

theorem Dummit_Foote_exercise_1_1_20 {G : Type*} [Group G] {x : G} :
  orderOf x = orderOf x⁻¹ := by
  -- Step 1: Apply the general lemma `orderOf_inv` which gives `orderOf x⁻¹ = orderOf x`.
  -- Step 1.1: Specialize the lemma at the chosen element `x` and record the resulting equality as `h`.
  have h : orderOf x⁻¹ = orderOf x := orderOf_inv x
  -- Step 2: Reorient the equality obtained in Step 1 so that it matches the required direction.
  -- Step 2.1: Take the symmetry of `h` to flip the sides and conclude.
  exact h.symm
