import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that characteristic subgroups are normal.
-/

/-Informal Proof

Let $H$ be a characteristic subgroup of $G$. By definition $\alpha(H) \subset H$ for every $\alpha \in \operatorname{Aut}(G)$. So, $H$ is in particular invariant under the inner automorphism. Let $\phi_g$ denote the conjugation automorphism by $g$. Then $\phi_g(H) \subset H \Longrightarrow$ $g H g^{-1} \subset H$. So, $H$ is normal.
-/

theorem Dummit_Foote_exercise_4_4_6a {G : Type*} [Group G] (H : Subgroup G)
  [Characteristic H] : Normal H  := by
  -- Step 1: Enable classical logic conveniences (e.g., functional extensionality on sets).
  classical
  -- Step 2: Unfold the definition of normality by constructing the required `conj_mem` witness.
  refine ⟨?_⟩
  -- Step 3: Fix an arbitrary element `n` of `H` and an arbitrary conjugating element `g : G`.
  intro n hn g
  -- Step 4: Use the characteristic property specialized to conjugation by `g` to obtain an equality of subgroups.
  have hCharacteristic : Characteristic H := inferInstance
  -- Step 4.1: Apply the characteristic invariance to the inner automorphism `MulAut.conj g`.
  have hFixed :
      H.comap (MulAut.conj g).toMonoidHom = H :=
    hCharacteristic.fixed (MulAut.conj g)
  -- Step 5: Translate the membership assumption `hn` through the equality of subgroups.
  have hComap :
      n ∈ H.comap (MulAut.conj g).toMonoidHom := by
    -- Step 5.1: View the subgroup equality as a membership equivalence evaluated at the element `n`.
    have hMembershipEquiv :
        n ∈ H.comap (MulAut.conj g).toMonoidHom ↔ n ∈ H :=
      (SetLike.ext_iff.mp hFixed) n
    -- Step 5.2: Move from the right-to-left direction of the equivalence using `hn : n ∈ H`.
    exact hMembershipEquiv.mpr hn
  -- Step 6: Unfold the definition of membership in the comap to conclude that the conjugate lies in `H`.
  simpa [Subgroup.mem_comap, MulAut.conj_apply] using hComap
