import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Let $A$ be an abelian group and let $B$ be a subgroup of $A$. Prove that $A / B$ is abelian.
-/

/-Informal Proof

Lemma: Let $G$ be a group. If $|G|=2$, then $G \cong Z_2$.
Proof: Since $G=\{e a\}$ has an identity element, say $e$, we know that $e e=e, e a=a$, and $a e=a$. If $a^2=a$, we have $a=e$, a contradiction. Thus $a^2=e$. We can easily see that $G \cong Z_2$.

If $A$ is abelian, every subgroup of $A$ is normal; in particular, $B$ is normal, so $A / B$ is a group. Now let $x B, y B \in A / B$. Then
$$
(x B)(y B)=(x y) B=(y x) B=(y B)(x B) .
$$
Hence $A / B$ is abelian.
-/

theorem Dummit_Foote_exercise_3_1_3a {A : Type*} [CommGroup A] (B : Subgroup A) :
  ∀ a b : A ⧸ B, a*b = b*a := by
  -- Step 1: Introduce arbitrary cosets `a` and `b` in the quotient group `A ⧸ B`
  --         so that we can reason pointwise about their product.
  intro a b
  -- Step 2: Apply the commutativity law in the quotient commutative group `A ⧸ B`,
  --         which it inherits from the ambient commutative group `A`.
  -- Step 2.1: The lemma `mul_comm a b` explicitly states the desired equality, so we conclude with it.
  simpa using (mul_comm a b)
