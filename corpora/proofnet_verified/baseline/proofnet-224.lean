import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that if $H$ and $K$ are normal subgroups of a group $G$ then their intersection $H \cap K$ is also a normal subgroup of $G$.
-/

/-Informal Proof

Suppose $H$ and $K$ are normal subgroups of $G$. We already know that $H \cap K$ is a subgroup of $G$, so we need to show that it is normal. Choose any $g \in G$ and any $x \in H \cap K$. Since $x \in H$ and $H \unlhd G$, we know $g x g^{-1} \in H$. Likewise, since $x \in K$ and $K \unlhd G$, we have $g x g^{-1} \in K$. Therefore $g x g^{-1} \in H \cap K$. This shows that $g(H \cap K) g^{-1} \subseteq H \cap K$, and this is true for all $g \in G$. By Theorem 6 (5) (which we will prove in Exercise 3.1.25), this is enough to show that $H \cap K \unlhd G$.
-/

theorem Dummit_Foote_exercise_3_1_22a (G : Type*) [Group G] (H K : Subgroup G)
  [Normal H] [Normal K] :
  Normal (H ⊓ K) := by
  -- Step 1: unpackage the goal `Normal (H ⊓ K)` so that we can directly
  --         construct the `conj_mem` witness demanded by the structure.
  refine ⟨?_⟩
  -- Step 1.1: fix an arbitrary `x` from the intersection together with a
  --           conjugating element `g : G`.
  intro x hx g
  -- Step 2: unpack the membership information coming from `hx` so we know
  --         that `x` individually belongs to both `H` and `K`.
  have hxH : x ∈ H := by
    -- Step 2.1: the left projection of `hx : x ∈ H ⊓ K` yields `x ∈ H`.
    exact hx.1
  have hxK : x ∈ K := by
    -- Step 2.2: the right projection of `hx : x ∈ H ⊓ K` yields `x ∈ K`.
    exact hx.2
  -- Step 3: use the normality of `H` and `K` to show the conjugate of `x`
  --         by `g` remains in each subgroup separately.
  have conjH : g * x * g⁻¹ ∈ H := by
    -- Step 3.1: apply the `conj_mem` field coming from the normality of `H`.
    simpa using (inferInstance : H.Normal).conj_mem x hxH g
  have conjK : g * x * g⁻¹ ∈ K := by
    -- Step 3.2: apply the corresponding `conj_mem` field for `K`.
    simpa using (inferInstance : K.Normal).conj_mem x hxK g
  -- Step 4: reassemble the two membership conclusions to finish the proof
  --         that the conjugate lies inside the intersection `H ⊓ K`.
  exact ⟨conjH, conjK⟩
