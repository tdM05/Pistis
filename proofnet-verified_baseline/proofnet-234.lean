import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Let $G$ be a group with subgroups $H$ and $K$ with $H \leq K$. Prove that if $H$ is characteristic in $K$ and $K$ is normal in $G$ then $H$ is normal in $G$.
-/

/-Informal Proof

We prove that $H$ is invariant under every inner automorphism of $G$. Consider a inner automorphism $\phi_g$ of $G$. Now, $\left.\phi_g\right|_K$ is a automorphism of $K$ because $K$ is normal in $G$. But $H$ is a characteristic subgroup of $K$, so $\left.\phi_g\right|_K(H) \subset H$, so in general $\phi_g(H) \subset H$. Hence $H$ is characteristic in $G$.
-/

theorem Dummit_Foote_exercise_4_4_8a {G : Type*} [Group G] (H K : Subgroup G)
  (hHK : H ≤ K) [hHK1 : (H.subgroupOf K).Characteristic] [hK : K.Normal] :
  H.Normal := by
  -- Step 1: Work in the classical logic setting so that `simp` can unfold subtype equalities.
  classical
  -- Step 2: View `H` inside `K`, use characteristic + normality to conclude that its image in `G` is normal.
  -- Step 2.1: The general instance `normal_of_characteristic_of_normal` supplies this normality automatically.
  have hImageNormal : ((H.subgroupOf K).map K.subtype).Normal := inferInstance
  -- Step 3: Invoke the canonical lemma `map_subgroupOf_eq_of_le` to identify this image with `H`.
  -- Step 3.1: This lemma rewrites the map along the inclusion `H ≤ K` straight back to `H`.
  have hImage_eq_H : ((H.subgroupOf K).map K.subtype) = H :=
    (Subgroup.map_subgroupOf_eq_of_le hHK)
  -- Step 4: Rewrite the normality from Step 2 along the equality from Step 3 to obtain `H.Normal` directly.
  simpa [hImage_eq_H] using hImageNormal
