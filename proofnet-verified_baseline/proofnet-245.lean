import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Let $\varphi: R \rightarrow S$ be a surjective homomorphism of rings. Prove that the image of the center of $R$ is contained in the center of $S$.
-/

/-Informal Proof

Suppose $r \in \varphi[Z(R)]$. Then $r=\varphi(z)$ for some $z \in Z(R)$. Now let $x \in S$. Since $\varphi$ is surjective, we have $x=\varphi y$ for some $y \in R$. Now
$$
x r=\varphi(y) \varphi(z)=\varphi(y z)=\varphi(z y)=\varphi(z) \varphi(y)=r x .
$$
Thus $r \in Z(S)$.
-/

theorem Dummit_Foote_exercise_7_3_16 {R S : Type*} [Ring R] [Ring S]
   {φ : R →+* S} (hf : Function.Surjective φ) :
   φ '' (center R) ⊆ center S := by
  -- Step 1: Fix an arbitrary element of the image; unpack it as φ z with z central in R.
  intro s hs
  rcases hs with ⟨z, hz, rfl⟩
  -- Step 2: Translate the statement "φ z is central in S" into pairwise commutation statements.
  apply (Semigroup.mem_center_iff).2
  -- Step 3: Choose an arbitrary element t of S and pull it back to R using surjectivity of φ.
  intro t
  obtain ⟨r, rfl⟩ := hf t
  -- Step 4: Extract the commutation relation inside R guaranteed by centrality of z.
  have hz_comm := (Semigroup.mem_center_iff.mp hz) r
  -- Step 5: Apply φ to that commutation relation and use the homomorphism property to translate it to S.
  have := congrArg φ hz_comm
  -- Step 6: Use the homomorphism property to convert the mapped equality into the desired commutation in S.
  simpa [map_mul] using this
